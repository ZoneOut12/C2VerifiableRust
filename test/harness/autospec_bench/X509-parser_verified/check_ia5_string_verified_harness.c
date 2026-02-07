// ========== Original Code (with ACSL) ==========
#include <stdint.h>
#include <unistd.h>
#include <string.h>

#define X509_FILE_NUM 1
#define X509_FILE_LINE_NUM_ERR ((X509_FILE_NUM * 100000))

/*@
	requires len > 0;
	requires \valid_read(buf + (0 .. (len - 1)));
	ensures \result < 0 || \result == 0;
	ensures (len == 0) ==> \result < 0;
	ensures \result == 0 ==> \forall integer i; 0 <= i < len ==> (buf[i] <= 0x7f);
	ensures \result == -X509_FILE_LINE_NUM_ERR ==> \exists integer i; 0 <= i < len && buf[i] > 0x7f;
	ensures \exists integer i; 0 <= i < len && buf[i] > 0x7f ==> \result == -X509_FILE_LINE_NUM_ERR;
	assigns \nothing;
*/
static int check_ia5_string(const uint8_t *buf, uint32_t len)
{
	int ret;
	uint32_t i;

	if ((buf == NULL) || (len == 0)) {
		ret = -X509_FILE_LINE_NUM_ERR;
		goto out;
	}

	/*@
		loop invariant \forall integer x ; 0 <= x < i ==> (buf[x] <= 0x7f);
		loop invariant ret ==0 ==> \forall integer x ; 0 <= x < i ==> (buf[x] <= 0x7f);
		loop assigns i;
		loop variant (len - i);
	*/
	for (i = 0; i < len; i++) {
		if (buf[i] > 0x7f) {
			ret = -X509_FILE_LINE_NUM_ERR;
			goto out;
		}
	}

	ret = 0;

out:
	return ret;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid buffer with ASCII characters A-E
void test_case_1() {
	uint8_t buf[] = {0x41, 0x42, 0x43, 0x44, 0x45};
	uint32_t len = 5;
	int result = check_ia5_string(buf, len);
	printf("test_case_1: %d\n", result); // Expected: 0
}

// Test case 2: Buffer with maximum allowed IA5 values (0x7F)
void test_case_2() {
	uint8_t buf[] = {0x7F, 0x7F, 0x7F};
	uint32_t len = 3;
	int result = check_ia5_string(buf, len);
	printf("test_case_2: %d\n", result); // Expected: 0
}

// Test case 3: Buffer with null, space, and tilde characters
void test_case_3() {
	uint8_t buf[] = {0x00, 0x20, 0x7E};
	uint32_t len = 3;
	int result = check_ia5_string(buf, len);
	printf("test_case_3: %d\n", result); // Expected: 0
}

// Test case 4: Buffer with lowercase letter, digit, and space
void test_case_4() {
	uint8_t buf[] = {0x61, 0x30, 0x20};
	uint32_t len = 3;
	int result = check_ia5_string(buf, len);
	printf("test_case_4: %d\n", result); // Expected: 0
}

// Test case 5: Single byte buffer with IA5 control character (LF)
void test_case_5() {
    uint8_t buf[] = {0x0A};  // '\n'
    uint32_t len = 1;
    int result = check_ia5_string(buf, len);
    printf("test_case_5: %d\n", result); // Expected: 0
}

// Test case 6: len = 0 violates precondition
void test_case_6() {
	uint8_t buf[] = {0x41};
	uint32_t len = 0;
	int result = check_ia5_string(buf, len); // Frama-C should flag this
}

// Test case 7: NULL buffer violates precondition
void test_case_7() {
	uint32_t len = 5;
	int result = check_ia5_string(NULL, len); // Frama-C should flag this
}

// Test case 8: Minimum valid length with maximum IA5 value
void test_case_8() {
	uint8_t buf[] = {0x7F};
	uint32_t len = 1;
	int result = check_ia5_string(buf, len);
	printf("test_case_8: %d\n", result); // Expected: 0
}

// Test case 9: Minimum valid length with invalid IA5 value
void test_case_9() {
	uint8_t buf[] = {0x80};
	uint32_t len = 1;
	int result = check_ia5_string(buf, len);
	printf("test_case_9: %d\n", result); // Expected: -100000
}

// Harness entry point
void test_harness_check_ia5_string() {
	test_case_1();
	test_case_2();
	test_case_3();
	test_case_4();
	test_case_5();
	test_case_8();
	test_case_9();
	// test_case_6 and test_case_7 intentionally not called
}
void test_case_6() {
    uint8_t *buf = NULL;
    uint32_t len = 0;
    int result = check_ia5_string(buf, len);
    assert(result != 0);
}

void test_case_7() {
    uint8_t *buf = NULL;
    uint32_t len = 5;
    int result = check_ia5_string(buf, len);
    assert(result != 0);
}