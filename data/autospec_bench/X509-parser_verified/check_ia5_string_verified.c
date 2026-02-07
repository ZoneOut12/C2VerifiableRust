// from x509-parser
// https://github.com/ANSSI-FR/x509-parser/blob/6f3bae3c52989180df6af46da1acb0329315b82a/src/x509-common.c#L2235-L2273

#include <stdint.h>
#include <unistd.h>
#include <string.h>

#define X509_FILE_NUM 1 /* See x509-utils.h for rationale */

/*
 * Historically, we used -__LINE__ as return value. This worked well when
 * the parser was a single file. Now that we have multiple files in the
 * project, we encode a unique numerical identifier for each file in the
 * return value. For that to work, we need each *implementation* file
 * to define a unique value for X509_FILE_NUM at its beginning.
 */
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
		//ERROR_TRACE_APPEND(X509_FILE_LINE_NUM_ERR);
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


int main() {
	uint8_t buf[5];
	uint32_t len = 5;

	int ret = check_ia5_string(&buf[0], len);
	//@ assert ret == -X509_FILE_LINE_NUM_ERR ==> \exists integer i; 0 <= i < len && buf[i] > 0x7f;
	//@ assert ret == 0 ==> \forall integer i; 0 <= i < len ==> (buf[i] <= 0x7f);

	return ret;
}