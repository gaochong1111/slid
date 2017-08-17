#ifndef SL_SAT_H
#define SL_SAT_H

#include <vector>
#include <set>

#include <z3.h>
#include "sl_abstr.h"

class sl_sat {
public:
	static bool check_sat(Z3_context, Z3_ast);
	static std::vector<std::set<int>> get_equivalence_class(sl_abstr&);
};


#endif //sl_sat.h
