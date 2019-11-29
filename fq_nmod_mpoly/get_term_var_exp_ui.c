/*
    Copyright (C) 2019 Daniel Schultz

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <http://www.gnu.org/licenses/>.
*/

#include "fq_nmod_mpoly.h"

ulong fq_nmod_mpoly_get_term_var_exp_ui(const fq_nmod_mpoly_t A, slong i,
                                      slong var, const fq_nmod_mpoly_ctx_t ctx)
{
    slong N;

    if ((ulong) i >= (ulong) A->length)
    {
        flint_throw(FLINT_ERROR,
                    "Index out of range in fq_nmod_mpoly_get_term_var_exp_ui");
    }

    N = mpoly_words_per_exp(A->bits, ctx->minfo);
    return mpoly_get_monomial_var_exp_ui(A->exps + N*i, var, A->bits, ctx->minfo);
}