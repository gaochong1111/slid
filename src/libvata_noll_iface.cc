/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure                                               */
/*                                                                        */
/*  Copyright (C) 2012-2014                                               */
/*    LIAFA (University of Paris Diderot and CNRS)                        */
/*    VeriFIT (Brno University of Technology)                             */
/*                                                                        */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 3.                                                */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 3.                  */
/*  for more details (enclosed in the file LICENSE).                      */
/*                                                                        */
/**************************************************************************/

// VATA header files
#include <vata/explicit_tree_aut.hh>
#include <vata/serialization/timbuk_serializer.hh>

#include "libvata_noll_iface.h"

// to catch strange behaviour
#ifndef __cplusplus
	#error "Needs a C++ compiler!"
#endif

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

using TreeAut           = VATA::ExplicitTreeAut;
using TreeAutSymbol     = TreeAut::SymbolType;
using StringSymbolType  = TreeAut::StringSymbolType;

typedef struct type_noll_ta_t
{
	TreeAut ta;
} noll_ta_t;


// TODO: use sth similar to DirectAlphabet and pass directly pointers to the
// symbols in SPEN (they are unique!)
class NollAlphabet : public TreeAut::AbstractAlphabet
{
private:  // data members

	// TreeAut::SymbolDict symbolDict_{};
	// TreeAutSymbol nextSymbol_ = 0;

public:   // methods

	static const noll_ta_symbol_t* vata_to_noll_symbol(const TreeAutSymbol& vata_symb)
	{
		const noll_ta_symbol_t* noll_symb =
			reinterpret_cast<const noll_ta_symbol_t*>(vata_symb);
		assert(nullptr != noll_symb);
		return noll_symb;
	}

	static TreeAutSymbol noll_to_vata_symbol(const noll_ta_symbol_t* noll_symb)
	{
		assert(nullptr != noll_symb);
		TreeAutSymbol vata_symb = reinterpret_cast<TreeAutSymbol>(noll_symb);
		return vata_symb;
	}

	virtual FwdTranslatorPtr GetSymbolTransl() override
	{
		assert(false);
		// FwdTranslator* fwdTransl = new
		// 	TreeAut::StringSymbolToSymbolTranslWeak{symbolDict_,
		// 	[&](const TreeAut::StringSymbolType&){return nextSymbol_++;}};
    //
		// return FwdTranslatorPtr(fwdTransl);
	}

	virtual BwdTranslatorPtr GetSymbolBackTransl() override
	{
		class NollBackTranslator : public NollAlphabet::BwdTranslator
		{
			virtual StringSymbolType operator()(const TreeAutSymbol& value) override
			{
				return const_cast<const NollBackTranslator*>(this)->operator()(value);
			}

			virtual StringSymbolType operator()(const TreeAutSymbol& value) const override
			{
				return StringSymbolType(noll_ta_symbol_get_str(
					vata_to_noll_symbol(value)), 0);
			}
		};

		BwdTranslator* bwdTransl = new NollBackTranslator();

		return BwdTranslatorPtr(bwdTransl);
	}
};

/* ====================================================================== */
/* Global variables */
/* ====================================================================== */

static VATA::ExplicitTreeAut::AlphabetType nollAlph(new NollAlphabet);

/* ====================================================================== */
/* Functions */
/* ====================================================================== */

vata_ta_t* vata_create_ta()
{
	vata_ta_t* ta = new vata_ta_t;

	ta->ta.SetAlphabet(nollAlph);

	return ta;
}

void vata_free_ta(
	vata_ta_t*       ta)
{
	delete ta;
}

void vata_set_state_root(
	vata_ta_t*          ta,
	vata_state_t        state)
{
	// check whether the input is sane
	assert(nullptr != ta);

	ta->ta.SetStateFinal(state);
}

void vata_add_transition(
	vata_ta_t*                ta,
	vata_state_t              parent,
	const vata_symbol_t*      symbol,
	const noll_uid_array*     children)
{
	// check that the input is sane
	assert(nullptr != ta);
	assert(nullptr != ta->ta.GetAlphabet());
	assert(nullptr != symbol);

	size_t numChildren = 0;
	TreeAut::StateTuple tupChildren;
	if (nullptr != children)
	{
		size_t numChildren = noll_vector_size(children);
		tupChildren = TreeAut::StateTuple(
			noll_vector_array(children),
			noll_vector_array(children) + numChildren);
	}

	TreeAutSymbol taSym = NollAlphabet::noll_to_vata_symbol(symbol);

	ta->ta.AddTransition(tupChildren, taSym, parent);
}


void vata_print_ta(
	const vata_ta_t*        ta)
{
	// check that the input is sane
	assert(nullptr != ta);

	//std::cout << "\nTreeAutomaton:  <*(((><       <-- this is a fish, not a TA!\n\n";

	VATA::Serialization::TimbukSerializer serializer;
	std::cout << ta->ta.DumpToString(serializer);
}


bool vata_check_inclusion(
	const vata_ta_t*        smaller_ta,
	const vata_ta_t*        bigger_ta)
{
	// check the sanity of passed paremeters
	assert(nullptr != smaller_ta);
	assert(nullptr != bigger_ta);

	// the params may be used to specify the exact inclusion checking
	// algorithm
	VATA::InclParam params;
	return TreeAut::CheckInclusion(smaller_ta->ta, bigger_ta->ta, params);
}


void vata_translate_symbols(
	vata_ta_t*                        ta,
	vata_symbol_translate_fncptr      transl)
{
	assert(nullptr != ta);
	assert(nullptr != transl);

	class Translator : public TreeAut::AbstractSymbolTranslateF
	{
	private:

		vata_symbol_translate_fncptr translFunc_;

	public:

		virtual TreeAutSymbol operator()(const TreeAutSymbol& symb) override
		{
			assert(nullptr != translFunc_);
			assert(nullptr != &symb);

			return NollAlphabet::noll_to_vata_symbol(
				translFunc_(
					NollAlphabet::vata_to_noll_symbol(symb)
				));
		}

	public:

		explicit Translator(vata_symbol_translate_fncptr translFunc) :
			translFunc_(translFunc)
		{
			assert(nullptr != translFunc_);
		}
	};

	Translator symTransl(transl);
	ta->ta = ta->ta.TranslateSymbols(symTransl);
}
