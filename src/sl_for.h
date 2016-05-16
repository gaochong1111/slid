#ifndef SL_FOR_H
#define SL_FOR_H

#include <vector>

#include "noll_form.h"

class sl_for {
public:
	sl_for(): nollf(nullptr) {}
	sl_for(noll_form_t*);
	/*
	 *sl_for(sl_for&);
	 *sl_for& operator=(sl_for&);
	 */

	void init(noll_form_t*);

	noll_form_t* nollf;
	std::vector<noll_space_t*> sp_atoms;
};

#endif //sl_for.h
