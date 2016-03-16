/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    seq_rewriter.cpp

Abstract:

    Basic rewriting rules for sequences constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2015-12-5

Notes:

--*/

#include"seq_rewriter.h"
#include"arith_decl_plugin.h"
#include"ast_pp.h"
#include"ast_util.h"


br_status seq_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    
    switch(f->get_decl_kind()) {

    case OP_SEQ_UNIT:
    case OP_SEQ_EMPTY:

    case OP_RE_PLUS:
    case OP_RE_STAR:
    case OP_RE_OPTION:
    case OP_RE_RANGE:
    case OP_RE_CONCAT:
    case OP_RE_UNION:
    case OP_RE_INTERSECT:
    case OP_RE_LOOP:
    case OP_RE_EMPTY_SET:
    case OP_RE_FULL_SET:
    case OP_RE_EMPTY_SEQ:
    case OP_RE_OF_PRED:
        return BR_FAILED;

    // string specific operators.
    case OP_STRING_CONST:
        return BR_FAILED;
    case OP_SEQ_CONCAT: 
        SASSERT(num_args == 2);
        return mk_seq_concat(args[0], args[1], result);
    case OP_SEQ_LENGTH:
        SASSERT(num_args == 1);
        return mk_str_length(args[0], result);
    case OP_SEQ_EXTRACT:
        SASSERT(num_args == 3);
        return mk_str_substr(args[0], args[1], args[2], result);
    case OP_SEQ_CONTAINS: 
        SASSERT(num_args == 2);
        return mk_str_strctn(args[0], args[1], result);
    case OP_SEQ_AT:
        SASSERT(num_args == 2);
        return mk_str_at(args[0], args[1], result); 
    case OP_STRING_STRIDOF: 
        SASSERT(num_args == 3);
        return mk_str_stridof(args[0], args[1], args[2], result);
    case OP_STRING_STRREPL: 
        SASSERT(num_args == 3);
        return mk_str_strrepl(args[0], args[1], args[2], result);
    case OP_SEQ_PREFIX: 
        SASSERT(num_args == 2);
        return mk_seq_prefix(args[0], args[1], result);
    case OP_SEQ_SUFFIX: 
        SASSERT(num_args == 2);
        return mk_seq_suffix(args[0], args[1], result);
    case OP_STRING_ITOS: 
        SASSERT(num_args == 1);
        return mk_str_itos(args[0], result);
    case OP_STRING_STOI: 
        SASSERT(num_args == 1);
        return mk_str_stoi(args[0], result);
    case OP_SEQ_TO_RE:
    case OP_SEQ_IN_RE:
    case OP_REGEXP_LOOP: 
        return BR_FAILED;
    case _OP_STRING_CONCAT:
    case _OP_STRING_PREFIX:
    case _OP_STRING_SUFFIX:
    case _OP_STRING_STRCTN:
    case _OP_STRING_LENGTH:
    case _OP_STRING_CHARAT:
    case _OP_STRING_IN_REGEXP: 
    case _OP_STRING_TO_REGEXP: 
    case _OP_STRING_SUBSTR: 

        UNREACHABLE();
    }
    return BR_FAILED;
}

/*
   string + string = string
   a + (b + c) = (a + b) + c
   a + "" = a
   "" + a = a
   (a + string) + string = a + string
*/
br_status seq_rewriter::mk_seq_concat(expr* a, expr* b, expr_ref& result) {
    std::string s1, s2;
    expr* c, *d;
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);
    if (isc1 && isc2) {
        result = m_util.str.mk_string(s1 + s2);
        return BR_DONE;
    }
    if (m_util.str.is_concat(b, c, d)) {
        result = m_util.str.mk_concat(m_util.str.mk_concat(a, c), d);
        return BR_REWRITE2;
    }
    if (m_util.str.is_empty(a)) {
        result = b;
        return BR_DONE;
    }
    if (m_util.str.is_empty(b)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.str.is_concat(a, c, d) && 
        m_util.str.is_string(d, s1) && isc2) {
        result = m_util.str.mk_concat(c, m_util.str.mk_string(s1 + s2));
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_length(expr* a, expr_ref& result) {
    std::string b;
    m_es.reset();
    m_util.str.get_concat(a, m_es);
    size_t len = 0;
    size_t j = 0;
    for (unsigned i = 0; i < m_es.size(); ++i) {
        if (m_util.str.is_string(m_es[i], b)) {
            len += b.length();
        }
        else {
            m_es[j] = m_es[i];
            ++j;
        }
    }
    if (j == 0) {
        result = m_autil.mk_numeral(rational(len, rational::ui64()), true);
        return BR_DONE;
    }
    if (j != m_es.size()) {
        expr_ref_vector es(m());        
        for (unsigned i = 0; i < j; ++i) {
            es.push_back(m_util.str.mk_length(m_es[i]));
        }
        if (len != 0) {
            es.push_back(m_autil.mk_numeral(rational(len, rational::ui64()), true));
        }
        result = m_autil.mk_add(es.size(), es.c_ptr());
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_substr(expr* a, expr* b, expr* c, expr_ref& result) {
    std::string s;
    rational pos, len;
    if (m_util.str.is_string(a, s) && m_autil.is_numeral(b, pos) && m_autil.is_numeral(c, len) &&
        pos.is_unsigned() && len.is_unsigned() && pos.get_unsigned() <= s.length()) {
        unsigned _pos = pos.get_unsigned();
        unsigned _len = len.get_unsigned();
        result = m_util.str.mk_string(s.substr(_pos, _len));
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_strctn(expr* a, expr* b, expr_ref& result) {
    std::string c, d;
    if (m_util.str.is_string(a, c) && m_util.str.is_string(b, d)) {
        result = m().mk_bool_val(0 != strstr(d.c_str(), c.c_str()));
        return BR_DONE;
    }
    // check if subsequence of a is in b.
    ptr_vector<expr> as, bs;
    m_util.str.get_concat(a, as);
    m_util.str.get_concat(b, bs);
    bool found = false;
    for (unsigned i = 0; !found && i < bs.size(); ++i) {
        if (as.size() > bs.size() - i) break;
        unsigned j = 0;
        for (; j < as.size() && as[j] == bs[i+j]; ++j) {};
        found = j == as.size();
    }
    if (found) {
        result = m().mk_true();
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_at(expr* a, expr* b, expr_ref& result) {
    std::string c;
    rational r;
    if (m_util.str.is_string(a, c) && m_autil.is_numeral(b, r) && r.is_unsigned()) {
        unsigned j = r.get_unsigned();
        if (j < c.length()) {
            char ch = c[j];
            c[0] = ch;
            c[1] = 0;
            result = m_util.str.mk_string(c);
            return BR_DONE;
        }
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_stridof(expr* a, expr* b, expr* c, expr_ref& result) {
    std::string s1, s2;
    rational r;
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);

    if (isc1 && isc2 && m_autil.is_numeral(c, r) && r.is_unsigned()) {
        for (unsigned i = r.get_unsigned(); i < s1.length(); ++i) {
            if (strncmp(s1.c_str() + i, s2.c_str(), s2.length()) == 0) {
                result = m_autil.mk_numeral(rational(i) - r, true);
                return BR_DONE;
            }
        }
        result = m_autil.mk_numeral(rational(-1), true);
        return BR_DONE;
    }
    if (m_autil.is_numeral(c, r) && r.is_neg()) {
        result = m_autil.mk_numeral(rational(-1), true);
        return BR_DONE;
    }
    
    if (m_util.str.is_empty(b)) {
        result = c;
        return BR_DONE;
    }
    // Enhancement: walk segments of a, determine which segments must overlap, must not overlap, may overlap.
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_strrepl(expr* a, expr* b, expr* c, expr_ref& result) {
    std::string s1, s2, s3;
    if (m_util.str.is_string(a, s1) && m_util.str.is_string(b, s2) && 
        m_util.str.is_string(c, s3)) {
        std::ostringstream buffer;
        for (size_t i = 0; i < s1.length(); ) {
            if (strncmp(s1.c_str() + i, s2.c_str(), s2.length()) == 0) {
                buffer << s3;
                i += s2.length();
            }
            else {
                buffer << s1[i];
                ++i;
            }
        }
        result = m_util.str.mk_string(buffer.str());
        return BR_DONE;
    }
    if (b == c) {
        result = a;
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_prefix(expr* a, expr* b, expr_ref& result) {
    TRACE("seq", tout << mk_pp(a, m()) << " " << mk_pp(b, m()) << "\n";);
    std::string s1, s2;
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);
    if (isc1 && isc2) {
        bool prefix = s1.length() <= s2.length();
        for (unsigned i = 0; i < s1.length() && prefix; ++i) {
            prefix = s1[i] == s2[i];
        }
        result = m().mk_bool_val(prefix);
        return BR_DONE;
    }
    if (m_util.str.is_empty(a)) {
        result = m().mk_true();
        return BR_DONE;
    }
    expr* a1 = m_util.str.get_leftmost_concat(a);
    expr* b1 = m_util.str.get_leftmost_concat(b);
    isc1 = m_util.str.is_string(a1, s1);
    isc2 = m_util.str.is_string(b1, s2);
    ptr_vector<expr> as, bs;

    if (a1 != b1 && isc1 && isc2) {
        if (s1.length() <= s2.length()) {
            if (strncmp(s1.c_str(), s2.c_str(), s1.length()) == 0) {
                if (a == a1) {
                    result = m().mk_true();
                    return BR_DONE;
                }               
                m_util.str.get_concat(a, as);
                m_util.str.get_concat(b, bs);
                SASSERT(as.size() > 1);
                s2 = std::string(s2.c_str() + s1.length(), s2.length() - s1.length());
                bs[0] = m_util.str.mk_string(s2);
                result = m_util.str.mk_prefix(m_util.str.mk_concat(as.size()-1, as.c_ptr()+1),
                                     m_util.str.mk_concat(bs.size(), bs.c_ptr()));
                return BR_REWRITE_FULL;
            }
            else {
                result = m().mk_false();
                return BR_DONE;
            }
        }
        else {
            if (strncmp(s1.c_str(), s2.c_str(), s2.length()) == 0) {
                if (b == b1) {
                    result = m().mk_false();
                    return BR_DONE;
                }
                m_util.str.get_concat(a, as);
                m_util.str.get_concat(b, bs);
                SASSERT(bs.size() > 1);
                s1 = std::string(s1.c_str() + s2.length(), s1.length() - s2.length());
                as[0] = m_util.str.mk_string(s1);
                result = m_util.str.mk_prefix(m_util.str.mk_concat(as.size(), as.c_ptr()),
                                     m_util.str.mk_concat(bs.size()-1, bs.c_ptr()+1));
                return BR_REWRITE_FULL;                
            }
            else {
                result = m().mk_false();
                return BR_DONE;
            }
        }        
    }
    if (a1 != b1) {
        return BR_FAILED;
    }
    m_util.str.get_concat(a, as);
    m_util.str.get_concat(b, bs);
    unsigned i = 0;
    for (; i < as.size() && i < bs.size() && as[i] == bs[i]; ++i) {};
    if (i == as.size()) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (i == bs.size()) {
        expr_ref_vector es(m());
        for (unsigned j = i; j < as.size(); ++j) {
            es.push_back(m().mk_eq(m_util.str.mk_empty(m().get_sort(a)), as[j]));
        }
        result = mk_and(es);
        return BR_REWRITE3;
    }
    if (i > 0) {
        a = m_util.str.mk_concat(as.size() - i, as.c_ptr() + i);
        b = m_util.str.mk_concat(bs.size() - i, bs.c_ptr() + i); 
        result = m_util.str.mk_prefix(a, b);
        return BR_DONE;
    }
    UNREACHABLE();
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_suffix(expr* a, expr* b, expr_ref& result) {
    if (a == b) {
        result = m().mk_true();
        return BR_DONE;
    }
    std::string s1, s2;
    if (m_util.str.is_empty(a)) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (m_util.str.is_empty(b)) {
        result = m().mk_eq(m_util.str.mk_empty(m().get_sort(a)), a);
        return BR_REWRITE3;
    }
    // concatenation is left-associative, so a2, b2 are not concatenations
    expr* a1, *a2, *b1, *b2;
    if (m_util.str.is_concat(a, a1, a2) && 
        m_util.str.is_concat(b, b1, b2) && a2 == b2) {
        result = m_util.str.mk_suffix(a1, b1);
        return BR_REWRITE1;
    }
    if (m_util.str.is_concat(b, b1, b2) && b2 == a) {
        result = m().mk_true();
        return BR_DONE;
    }
    bool isc1 = false;
    bool isc2 = false;
    
    if (m_util.str.is_concat(a, a1, a2) && m_util.str.is_string(a2, s1)) {
        isc1 = true;
    }
    else if (m_util.str.is_string(a, s1)) {
        isc1 = true;
        a2 = a;
        a1 = 0;
    }

    if (m_util.str.is_concat(b, b1, b2) && m_util.str.is_string(b2, s2)) {
        isc2 = true;
    }
    else if (m_util.str.is_string(b, s2)) {
        isc2 = true;
        b2 = b;
        b1 = 0;
    }
    if (isc1 && isc2) {
        if (s1.length() == s2.length()) {
            SASSERT(s1 != s2);
            result = m().mk_false();
            return BR_DONE;
        }
        else if (s1.length() < s2.length()) {
            bool suffix = true;
            for (unsigned i = 0; i < s1.length(); ++i) {
                suffix = s1[s1.length()-i-1] == s2[s2.length()-i-1];
            }
            if (suffix && a1 == 0) {
                result = m().mk_true();
                return BR_DONE;
            }
            else if (suffix) {
                s2 = std::string(s2.c_str(), s2.length()-s1.length());
                b2 = m_util.str.mk_string(s2);
                result = m_util.str.mk_suffix(a1, b1?m_util.str.mk_concat(b1, b2):b2);
                return BR_DONE;
            }
            else {
                result = m().mk_false();
                return BR_DONE;
            }
        }
        else {
            SASSERT(s1.length() > s2.length());
            if (b1 == 0) {
                result = m().mk_false();
                return BR_DONE;
            }
            bool suffix = true;
            for (unsigned i = 0; i < s2.length(); ++i) {
                suffix = s1[s1.length()-i-1] == s2[s2.length()-i-1];
            }
            if (suffix) {
                s1 = std::string(s1.c_str(), s1.length()-s2.length());
                a2 = m_util.str.mk_string(s1);
                result = m_util.str.mk_suffix(a1?m_util.str.mk_concat(a1, a2):a2, b1);
                return BR_DONE;
            }
            else {
                result = m().mk_false();
                return BR_DONE;
            }            
        }
    }

    return BR_FAILED;
}

br_status seq_rewriter::mk_str_itos(expr* a, expr_ref& result) {
    rational r;
    if (m_autil.is_numeral(a, r)) {
        result = m_util.str.mk_string(r.to_string());
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_stoi(expr* a, expr_ref& result) {
    std::string s;
    if (m_util.str.is_string(a, s)) {
        for (unsigned i = 0; i < s.length(); ++i) {
            if (s[i] == '-') { if (i != 0) return BR_FAILED; }
            else if ('0' <= s[i] && s[i] <= '9') continue;
            return BR_FAILED;            
        }
        rational r(s.c_str());
        result = m_autil.mk_numeral(r, true);
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_in_regexp(expr* a, expr* b, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_to_regexp(expr* a, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_re_concat(expr* a, expr* b, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_re_union(expr* a, expr* b, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_re_star(expr* a, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_re_plus(expr* a, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_re_opt(expr* a, expr_ref& result) {
    return BR_FAILED;
}
