/*
 * Copyright (c) 2017 Linaro, Ltd.
 * Copyright (c) 2026 Zephyr Project Contributors
 *
 * SPDX-License-Identifier: Apache-2.0
 */

/** @file
 * @brief SPI transport for the mcumgr SMP protocol.
 */

#include <string.h>
#include <zephyr/kernel.h>
#include <zephyr/device.h>
#include <zephyr/devicetree.h>
#include <zephyr/drivers/spi.h>
#include <zephyr/net_buf.h>
#include <zephyr/sys/crc.h>
#include <zephyr/sys/util.h>
#include <zephyr/sys/printk.h>
#include <zephyr/mgmt/mcumgr/mgmt/mgmt.h>
#include <zephyr/mgmt/mcumgr/smp/smp.h>
#include <zephyr/mgmt/mcumgr/transport/smp.h>

#include <mgmt/mcumgr/transport/smp_internal.h>

#define SMP_SPI_NODE DT_NODELABEL(smp_spi)

#if !DT_NODE_HAS_STATUS(SMP_SPI_NODE, okay)
#error "smp_spi devicetree node is missing or disabled"
#endif

static const struct device *const spi_dev = DEVICE_DT_GET(DT_PHANDLE(SMP_SPI_NODE, spi_dev));

#define SPI_BUF_SIZE CONFIG_MCUMGR_TRANSPORT_SPI_MTU
#define SPI_MODE_FLAGS (SPI_MODE_CPOL | SPI_MODE_CPHA)

#define HDR_MAGIC0 0xA5
#define HDR_MAGIC1 0x5A
#define HDR_SIZE   10
#define PAYLOAD_MAX (SPI_BUF_SIZE - HDR_SIZE)

#define FLAG_SYNC  0x01
#define FLAG_ACK   0x02
#define FLAG_DATA  0x04
#define FLAG_POLL  0x08
#define FLAG_RESET 0x10

#define SMP_HDR_SIZE 8
#define SEG_HDR_SIZE 6 /* u16 total, u16 offset, u8 flags, u8 rsv */
#define SEG_FLAG_LAST 0x01

#define SMP_BUF_MAX (PAYLOAD_MAX * 2)

#if defined(CONFIG_MCUMGR_TRANSPORT_SPI_REASSEMBLY)
#define SMP_REASSEMBLY_TIMEOUT_MS CONFIG_MCUMGR_TRANSPORT_SPI_REASSEMBLY_TIMEOUT_MS
#else
#define SMP_REASSEMBLY_TIMEOUT_MS 0
#endif

#if defined(CONFIG_MCUMGR_TRANSPORT_SPI_DEBUG)
#define SPI_DBG(...) printk(__VA_ARGS__)
#else
#define SPI_DBG(...) do { } while (0)
#endif

static uint8_t smp_buf[SMP_BUF_MAX];
static uint16_t smp_expected_len;
static uint16_t smp_filled;
static int64_t smp_last_seg_ms;

static uint8_t rx_buf[SPI_BUF_SIZE];
static uint8_t tx_buf[SPI_BUF_SIZE];
static uint8_t seg_payload[PAYLOAD_MAX];

static uint8_t smp_tx_buf[SMP_BUF_MAX];
static uint16_t smp_tx_len;
static uint16_t smp_tx_offset;
static bool smp_tx_ready;
static bool tx_seg_pending;
static uint16_t tx_seg_chunk;
static bool tx_seg_last;

static struct smp_transport smp_spi_transport;

static K_THREAD_STACK_DEFINE(smp_spi_stack,
			     CONFIG_MCUMGR_TRANSPORT_SPI_RX_THREAD_STACK_SIZE);
static struct k_thread smp_spi_thread_data;

static const struct spi_config smp_spi_cfg = {
	.operation = SPI_OP_MODE_SLAVE | SPI_WORD_SET(8) | SPI_TRANSFER_MSB |
		     SPI_MODE_FLAGS,
	.frequency = 50000U,
	.slave = CONFIG_MCUMGR_TRANSPORT_SPI_SLAVE,
};

static void build_frame(uint8_t flags, uint8_t seq, const uint8_t *payload, uint16_t payload_len);

static int smp_spi_tx_pkt(struct net_buf *nb)
{
	uint16_t len = nb->len;
	if (len > sizeof(smp_tx_buf)) {
		len = sizeof(smp_tx_buf);
	}
	memcpy(smp_tx_buf, nb->data, len);
	smp_tx_len = len;
	smp_tx_offset = 0;
	smp_tx_ready = true;
	SPI_DBG("SMP tx queued len=%u\n", len);
	smp_packet_free(nb);
	return 0;
}

static void prepare_tx_segment(uint8_t seq)
{
	if (tx_seg_pending) {
		return;
	}

	if (!(smp_tx_ready && smp_tx_offset < smp_tx_len)) {
		return;
	}

	uint16_t total = smp_tx_len;
	uint16_t offset = smp_tx_offset;
	uint16_t chunk = total - offset;
	uint16_t max_chunk = PAYLOAD_MAX - SEG_HDR_SIZE;
	if (chunk > max_chunk) {
		chunk = max_chunk;
	}

	uint8_t seg_flags = (offset + chunk >= total) ? SEG_FLAG_LAST : 0;
	seg_payload[0] = (uint8_t)(total & 0xFF);
	seg_payload[1] = (uint8_t)((total >> 8) & 0xFF);
	seg_payload[2] = (uint8_t)(offset & 0xFF);
	seg_payload[3] = (uint8_t)((offset >> 8) & 0xFF);
	seg_payload[4] = seg_flags;
	seg_payload[5] = 0;
	memcpy(&seg_payload[SEG_HDR_SIZE], &smp_tx_buf[offset], chunk);

	build_frame(FLAG_DATA, seq, seg_payload, (uint16_t)(SEG_HDR_SIZE + chunk));

	SPI_DBG("SMP tx seg offset=%u len=%u last=%u\n",
	       offset, chunk, (seg_flags & SEG_FLAG_LAST) ? 1 : 0);

	tx_seg_pending = true;
	tx_seg_chunk = chunk;
	tx_seg_last = (seg_flags & SEG_FLAG_LAST) ? true : false;
}

static uint16_t smp_spi_get_mtu(const struct net_buf *nb)
{
	ARG_UNUSED(nb);
	return SMP_BUF_MAX;
}

static void build_frame(uint8_t flags, uint8_t seq, const uint8_t *payload, uint16_t payload_len)
{
	if (payload_len > PAYLOAD_MAX) {
		payload_len = PAYLOAD_MAX;
	}

	memset(tx_buf, 0, sizeof(tx_buf));
	tx_buf[0] = HDR_MAGIC0;
	tx_buf[1] = HDR_MAGIC1;
	tx_buf[2] = flags;
	tx_buf[3] = seq;
	tx_buf[4] = (uint8_t)(payload_len & 0xFF);
	tx_buf[5] = (uint8_t)((payload_len >> 8) & 0xFF);

	if (payload_len > 0 && payload != NULL) {
		memcpy(tx_buf + HDR_SIZE, payload, payload_len);
	}

	uint32_t crc = crc32_ieee(tx_buf + HDR_SIZE, payload_len);
	tx_buf[6] = (uint8_t)(crc & 0xFF);
	tx_buf[7] = (uint8_t)((crc >> 8) & 0xFF);
	tx_buf[8] = (uint8_t)((crc >> 16) & 0xFF);
	tx_buf[9] = (uint8_t)((crc >> 24) & 0xFF);
}

static void smp_spi_thread(void *p1, void *p2, void *p3)
{
	ARG_UNUSED(p1);
	ARG_UNUSED(p2);
	ARG_UNUSED(p3);

	struct spi_buf rx = {
		.buf = rx_buf,
		.len = sizeof(rx_buf),
	};
	struct spi_buf tx = {
		.buf = tx_buf,
		.len = sizeof(tx_buf),
	};
	const struct spi_buf_set rx_set = {
		.buffers = &rx,
		.count = 1,
	};
	const struct spi_buf_set tx_set = {
		.buffers = &tx,
		.count = 1,
	};

	while (1) {
		int ret;
		int64_t now_ms = k_uptime_get();

#if defined(CONFIG_MCUMGR_TRANSPORT_SPI_REASSEMBLY)
		if (smp_expected_len > 0 &&
		    (now_ms - smp_last_seg_ms) > SMP_REASSEMBLY_TIMEOUT_MS) {
			SPI_DBG("SMP reassembly timeout; dropping partial message\n");
			smp_expected_len = 0;
			smp_filled = 0;
		}
#endif

		memset(rx_buf, 0, sizeof(rx_buf));
		ret = spi_transceive(spi_dev, &smp_spi_cfg, &tx_set, &rx_set);

		if (ret < 0) {
			printk("spi_transceive failed: %d\n", ret);
			k_sleep(K_MSEC(100));
			continue;
		}

		if (tx_seg_pending) {
			smp_tx_offset = (uint16_t)(smp_tx_offset + tx_seg_chunk);
			if (tx_seg_last || smp_tx_offset >= smp_tx_len) {
				smp_tx_ready = false;
			}
			tx_seg_pending = false;
		}

		if (rx_buf[0] != HDR_MAGIC0 || rx_buf[1] != HDR_MAGIC1) {
			continue;
		}

		uint8_t flags = rx_buf[2];
		uint8_t seq = rx_buf[3];
		uint16_t len = (uint16_t)rx_buf[4] | ((uint16_t)rx_buf[5] << 8);
		uint32_t crc_rx = (uint32_t)rx_buf[6] |
				  ((uint32_t)rx_buf[7] << 8) |
				  ((uint32_t)rx_buf[8] << 16) |
				  ((uint32_t)rx_buf[9] << 24);
		if (len > PAYLOAD_MAX) {
			len = PAYLOAD_MAX;
		}
		uint32_t crc_calc = crc32_ieee(rx_buf + HDR_SIZE, len);
		if (crc_calc != crc_rx) {
			printk("SPI bad-crc flags=%02x seq=%u len=%u\n", flags, seq, len);
			if (smp_expected_len > 0) {
				SPI_DBG("SMP reassembly reset due to CRC error\n");
				smp_expected_len = 0;
				smp_filled = 0;
			}
			continue;
		}

		if (flags == FLAG_ACK) {
			continue;
		}

		if (flags & FLAG_RESET) {
			SPI_DBG("SPI reset seq=%u\n", seq);
			smp_expected_len = 0;
			smp_filled = 0;
			smp_tx_ready = false;
			smp_tx_len = 0;
			smp_tx_offset = 0;
			tx_seg_pending = false;
			build_frame(FLAG_ACK, seq, NULL, 0);
		} else if (flags & FLAG_POLL) {
			SPI_DBG("SPI poll seq=%u\n", seq);
			if (!smp_tx_ready && !tx_seg_pending) {
				build_frame(FLAG_ACK, seq, NULL, 0);
			}
		} else if (flags & FLAG_SYNC) {
			SPI_DBG("SPI sync seq=%u\n", seq);
			smp_tx_ready = false;
			smp_tx_len = 0;
			smp_tx_offset = 0;
			tx_seg_pending = false;
			build_frame(FLAG_ACK, seq, NULL, 0);
		} else if (flags & FLAG_DATA) {
			SPI_DBG("SPI data seq=%u len=%u\n", seq, len);
#if !defined(CONFIG_MCUMGR_TRANSPORT_SPI_REASSEMBLY)
			if (len < SMP_HDR_SIZE) {
				build_frame(FLAG_ACK, seq, NULL, 0);
				continue;
			}
			struct net_buf *nb = smp_packet_alloc();
			if (nb) {
				if (len <= net_buf_tailroom(nb)) {
					net_buf_add_mem(nb, rx_buf + HDR_SIZE, len);
					SPI_DBG("SMP rx submit len=%u\n", len);
					smp_rx_req(&smp_spi_transport, nb);
				} else {
					printk("SMP buf too large for net_buf: %u\n", len);
					smp_packet_free(nb);
				}
			} else {
				printk("SMP packet alloc failed\n");
			}
			if (!tx_seg_pending) {
				build_frame(FLAG_ACK, seq, NULL, 0);
			}
			continue;
#endif
			if (len >= SEG_HDR_SIZE) {
				uint16_t total = (uint16_t)rx_buf[HDR_SIZE] |
						 ((uint16_t)rx_buf[HDR_SIZE + 1] << 8);
				uint16_t offset = (uint16_t)rx_buf[HDR_SIZE + 2] |
						  ((uint16_t)rx_buf[HDR_SIZE + 3] << 8);
				uint8_t sflags = rx_buf[HDR_SIZE + 4];
				uint16_t data_len = len - SEG_HDR_SIZE;
				SPI_DBG("SEG total=%u offset=%u data_len=%u last=%u\n",
				       total, offset, data_len, (sflags & SEG_FLAG_LAST) ? 1 : 0);

				if (total > sizeof(smp_buf)) {
					printk("SMP total too large: %u\n", total);
					build_frame(FLAG_ACK, seq, NULL, 0);
					continue;
				}

				if (offset == 0) {
					smp_expected_len = total;
					smp_filled = 0;
					smp_last_seg_ms = now_ms;
				}

				if (offset + data_len <= sizeof(smp_buf)) {
					memcpy(&smp_buf[offset], &rx_buf[HDR_SIZE + SEG_HDR_SIZE], data_len);
					smp_filled += data_len;
					smp_last_seg_ms = now_ms;
				}

				if ((sflags & SEG_FLAG_LAST) && smp_expected_len > 0 &&
				    smp_expected_len <= sizeof(smp_buf)) {
					if (smp_expected_len >= SMP_HDR_SIZE) {
						const uint8_t *smp = smp_buf;
						uint8_t op = smp[0];
						uint8_t fl = smp[1];
						uint16_t slen = (uint16_t)(smp[2] << 8) | smp[3];
						uint16_t sgroup = (uint16_t)(smp[4] << 8) | smp[5];
						uint8_t sseq = smp[6];
						uint8_t sid = smp[7];
						uint8_t op_dec = op & 0x07;
						uint8_t ver_dec = (op >> 3) & 0x03;
						SPI_DBG("SMP raw hdr bytes: %02x %02x %02x %02x %02x %02x %02x %02x\n",
						       smp[0], smp[1], smp[2], smp[3], smp[4], smp[5], smp[6], smp[7]);
						SPI_DBG("SMP hdr op=0x%02x (op=%u ver=%u) flags=%02x len=%u group=%u seq=%u id=%u\n",
						       op, op_dec, ver_dec, fl, slen, sgroup, sseq, sid);

						const struct mgmt_group *grp = mgmt_find_group(sgroup);
						const struct mgmt_handler *h = grp ? mgmt_get_handler(grp, sid) : NULL;
						SPI_DBG("MCUMGR lookup group=%u %s handler=%s read=%d write=%d\n",
						       sgroup,
						       grp ? "found" : "missing",
						       h ? "yes" : "no",
						       (h && h->mh_read) ? 1 : 0,
						       (h && h->mh_write) ? 1 : 0);
					}
					SPI_DBG("SMP reassembly done len=%u\n", smp_expected_len);

					struct net_buf *nb = smp_packet_alloc();
					if (nb) {
						if (smp_expected_len <= net_buf_tailroom(nb)) {
							net_buf_add_mem(nb, smp_buf, smp_expected_len);
							SPI_DBG("SMP rx submit len=%u\n", smp_expected_len);
							smp_rx_req(&smp_spi_transport, nb);
						} else {
							printk("SMP buf too large for net_buf: %u\n", smp_expected_len);
							smp_packet_free(nb);
						}
					} else {
						printk("SMP packet alloc failed\n");
					}

					smp_expected_len = 0;
					smp_filled = 0;
				}
			}
			if (!tx_seg_pending) {
				build_frame(FLAG_ACK, seq, NULL, 0);
			}
		} else {
			SPI_DBG("SPI frame flags=%02x seq=%u len=%u\n", flags, seq, len);
			if (!tx_seg_pending) {
				build_frame(FLAG_ACK, seq, NULL, 0);
			}
		}

		prepare_tx_segment(seq);
	}
}

static int smp_spi_init(void)
{
	int rc;

	if (!device_is_ready(spi_dev)) {
		printk("SPI device not ready\n");
		return -ENODEV;
	}

	smp_spi_transport.functions.output = smp_spi_tx_pkt;
	smp_spi_transport.functions.get_mtu = smp_spi_get_mtu;

	rc = smp_transport_init(&smp_spi_transport);
	if (rc != 0) {
		printk("SPI SMP transport init failed: %d\n", rc);
		return rc;
	}

	build_frame(FLAG_ACK, 0, NULL, 0);

	printk("SPI SMP transport initialized\n");

	k_thread_create(&smp_spi_thread_data, smp_spi_stack,
			K_THREAD_STACK_SIZEOF(smp_spi_stack),
			smp_spi_thread, NULL, NULL, NULL,
			CONFIG_MCUMGR_TRANSPORT_SPI_RX_THREAD_PRIO, 0, K_NO_WAIT);
	k_thread_name_set(&smp_spi_thread_data, "smp_spi");

#ifdef CONFIG_SMP_CLIENT
	static struct smp_client_transport_entry smp_spi_client_transport;
	smp_spi_client_transport.smpt = &smp_spi_transport;
	smp_spi_client_transport.smpt_type = SMP_SPI_TRANSPORT;
	smp_client_transport_register(&smp_spi_client_transport);
#endif

	return 0;
}

SYS_INIT(smp_spi_init, APPLICATION, CONFIG_APPLICATION_INIT_PRIORITY);
