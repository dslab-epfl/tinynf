#pragma once

static inline void rte_delay_us_callback_register (void(*userfunc)(unsigned int))
{
	// Nothing, we don't ever call sleep within the models
	(void) userfunc;
}
