/*
    Copyright (C) 2016 William Hart

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <http://www.gnu.org/licenses/>.
*/

#include <gmp.h>
#include "flint.h"
#include "fmpz.h"
#include "fmpz_vec.h"

void
_fmpz_vec_scalar_abs(fmpz * vec1, const fmpz * vec2, slong len2)
{
    slong i;
    for (i = 0; i < len2; i++)
        fmpz_abs(vec1 + i, vec2 + i);
}
