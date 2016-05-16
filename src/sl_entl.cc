#include "sl_entl.h"
#include "sl_entail.h"


int solve_entail()
{
	sl_entail s;
	
	return !(s.check_entail());
}
