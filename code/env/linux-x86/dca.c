#include "../dca.h"


// All references in this file are to the Intel 64 and IA-32 Architectures Software Developer's Manual,
// available at https://software.intel.com/en-us/download/intel-64-and-ia-32-architectures-sdm-combined-volumes-1-2a-2b-2c-2d-3a-3b-3c-3d-and-4

bool tn_dca_is_enabled(void)
{
	// We want the value of IA32_PLATFORM_DCA_CAP, which indicates if the platform supports DCA; Table 2-2 IA-32 Architectural MSRs indicates "if CPUID.01H: ECX[18] = 1"
	// So let's first check that this condition holds
	uint32_t result;
	__asm__ (
		"movl $1, %%eax\n\t"
		"cpuid"
		: "=c" (result)
		:
		: "eax", "ebx", "edx"
	);
	if ((result & (1 << 18)) == 0) {
		return false;
	}
	// Table 3-8 Information Returned by CPUID Instruction: "Initial EAX Value 09H: EAX, Value of bits [31:0] of IA32_PLATFORM_DCA_CAP MSR [...]"
	__asm__ (
		"movl $9, %%eax\n\t"
		"cpuid"
		: "=a" (result)
		:
		: "ebx", "ecx", "edx"
	);
	// INTERPRETATION: non-zero is yes, zero is no.
	return result != 0;
}

uint8_t tn_dca_get_id(void)
{
	// Table 3-8 Information Returned by CPUID Instruction: "Initial EAX Value 01H: EBX [...] Bits 31-24: Initial APIC ID."
	uint32_t result = 0;
	__asm__ (
		"movl $1, %%eax\n\t"
		"cpuid"
		: "=b" (result)
		:
		: "eax", "ecx", "edx"
	);
	return (uint8_t) (result >> 24);
}
