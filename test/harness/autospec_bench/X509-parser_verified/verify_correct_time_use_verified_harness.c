// ========== Original Code (with ACSL) ==========
#include <stdint.h>
#include <unistd.h>
#include <string.h>

typedef enum {
	CLASS_UNIVERSAL        = 0x00,
	CLASS_APPLICATION      = 0x01,
	CLASS_CONTEXT_SPECIFIC = 0x02,
	CLASS_PRIVATE          = 0x03
} tag_class;

typedef enum {
	ASN1_TYPE_BOOLEAN         = 0x01,
	ASN1_TYPE_INTEGER         = 0x02,
	ASN1_TYPE_BIT_STRING      = 0x03,
	ASN1_TYPE_OCTET_STRING    = 0x04,
	ASN1_TYPE_NULL            = 0x05,
	ASN1_TYPE_OID             = 0x06,
	ASN1_TYPE_ENUMERATED      = 0x0a,
	ASN1_TYPE_SEQUENCE        = 0x10,
	ASN1_TYPE_SET             = 0x11,
	ASN1_TYPE_PrintableString = 0x13,
	ASN1_TYPE_T61String       = 0x14,
	ASN1_TYPE_IA5String       = 0x16,
	ASN1_TYPE_UTCTime         = 0x17,
	ASN1_TYPE_GeneralizedTime = 0x18,
} asn1_type;

#define X509_FILE_NUM 3 
#define X509_FILE_LINE_NUM_ERR ((X509_FILE_NUM * 100000) + __LINE__)

/*@ ensures \result < 0 || \result == 0;
	ensures \result == -1 ==> (time_type != ASN1_TYPE_UTCTime && time_type != ASN1_TYPE_GeneralizedTime);
	ensures (time_type != ASN1_TYPE_UTCTime && time_type != ASN1_TYPE_GeneralizedTime) ==> \result == -1;
	assigns \nothing;
*/
int verify_correct_time_use(uint8_t time_type, uint16_t yyyy)
{
	int ret;

	switch (time_type) {
	case ASN1_TYPE_UTCTime:
		ret = (yyyy <= 2049) ? 0 : -X509_FILE_LINE_NUM_ERR;
		break;
	case ASN1_TYPE_GeneralizedTime:
		ret = (yyyy >= 2050) ? 0 : -X509_FILE_LINE_NUM_ERR;
		break;
	default:
		ret = -1;
		break;
	}

	return ret;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - UTCTime with valid year
void test_case_1() {
	int result = verify_correct_time_use(ASN1_TYPE_UTCTime, 2000);
	printf("test_case_1: %d\n", result);  // Expected: 0
}

// Test case 2: Valid - Testing the lower bound/early year for UTCTime
void test_case_2() {
	int result = verify_correct_time_use(ASN1_TYPE_UTCTime, 1950);
	printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - Non-time type
void test_case_3() {
	int result = verify_correct_time_use(ASN1_TYPE_PrintableString, 2023);
	printf("test_case_3: %d\n", result);  // Expected: -1
}

// Test case 4: Valid - GeneralizedTime with future year
void test_case_4() {
	int result = verify_correct_time_use(ASN1_TYPE_GeneralizedTime, 3000);
	printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - UTCTime with 20th century year
void test_case_5() {
	int result = verify_correct_time_use(ASN1_TYPE_UTCTime, 1990);
	printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - UTCTime at maximum allowed year
void test_case_6() {
	int result = verify_correct_time_use(ASN1_TYPE_UTCTime, 2049);
	printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - GeneralizedTime at minimum allowed year
void test_case_7() {
	int result = verify_correct_time_use(ASN1_TYPE_GeneralizedTime, 2050);
	printf("test_case_7: %d\n", result);  // Expected: 0
}

// Test case 8: Invalid - UTCTime with year exceeding maximum
void test_case_8() {
	int result = verify_correct_time_use(ASN1_TYPE_UTCTime, 2050);
	// Expected to return negative value (postcondition violation)
}

// Test case 9: Invalid - GeneralizedTime below minimum
void test_case_9() {
	int result = verify_correct_time_use(ASN1_TYPE_GeneralizedTime, 2049);
	// Expected to return negative value (postcondition violation)
}

// Harness entry point
void test_harness_verify_correct_time_use() {
	test_case_1();
	test_case_2();
	test_case_3();
	test_case_4();
	test_case_5();
	test_case_6();
	test_case_7();
	// Invalid test cases intentionally not called for formal verification
}
No additional test_case_N functions needed as all inputs are valid per empty preconditions.