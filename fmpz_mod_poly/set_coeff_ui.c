/*
    Copyright (C) 2011 Sebastian Pancratz
    Copyright (C) 2008, 2009 William Hart

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <https://www.gnu.org/licenses/>.
*/

#include <gmp.h>
#include <stdlib.h>
#include "flint.h"
#include "fmpz.h"
#include "fmpz_mod_poly.h"

void fmpz_mod_poly_set_coeff_ui(fmpz_mod_poly_t poly, slong n, ulong x)
{
    if (x == 0)
    {
       if (n >= poly->length)
          return;

       fmpz_zero(poly->coeffs + n);
    } else
    {
        fmpz_mod_poly_fit_length(poly, n + 1);

        if (n + 1 > poly->length)
        {
            flint_mpn_zero((mp_ptr) (poly->coeffs + poly->length), n - poly->length);
            poly->length = n + 1;
        }

        fmpz_set_ui(poly->coeffs + n, x);
        fmpz_mod(poly->coeffs + n, poly->coeffs + n, &(poly->p));
    }
    
    if (n == poly->length - 1) 
        _fmpz_mod_poly_normalise(poly); /* we may have set the leading coefficient to 0 */
}

