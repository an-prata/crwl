// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

#include<stdint.h>

#define ADDR 0
#define PACKET_BITS 48

#define RX_CLOCK 2
#define RX_DATA 3

#define TX_CLOCK 0
#define TX_DATA 1

#define POT_POSITIVE A4
#define POT_NEGATIVE A5

#define RECV_BIT(INT) INT <<= 1; \
  while (digitalRead(RX_CLOCK) == HIGH); \
	INT |= digitalRead(RX_DATA) == HIGH ? 1 : 0; \
	while (digitalRead(RX_CLOCK) == LOW); \

union Data {
  float speed;
  uint32_t bits;
};

float speed = 0.0;

void setup() {
	pinMode(RX_CLOCK, INPUT);
	pinMode(RX_DATA, INPUT);

	pinMode(TX_CLOCK, OUTPUT);
	pinMode(TX_DATA, OUTPUT);
}

void loop() {
	while (digitalRead(RX_CLOCK) == HIGH && digitalRead(RX_DATA) == LOW);

	if (!(digitalRead(RX_CLOCK) == HIGH && digitalRead(RX_DATA) == HIGH))
		return;

	uint8_t addr = 0;
	uint8_t cmd  = 0;
	Data    data = Data { .bits = 0 };

	for (uint8_t i = 0; i < sizeof addr * 8; i++)
    RECV_BIT(addr);

	for (uint8_t i = 0; i < sizeof cmd * 8; i++)
    RECV_BIT(cmd);
		
	for (uint8_t i = 0; i < sizeof data * 8; i++)
    RECV_BIT(data.bits);

	if (addr != ADDR)
		return;

	int speed_val = data.speed > 0.0 ? data.speed * 255.0 : data.speed * -255.0;

	if (speed > 0.0) {
		analogWrite(POT_POSITIVE, speed_val);
		analogWrite(POT_NEGATIVE, 0.0);
	} else {
		analogWrite(POT_POSITIVE, 0.0);
		analogWrite(POT_NEGATIVE, speed_val);
	}
}
