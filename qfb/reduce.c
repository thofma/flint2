/*=============================================================================

    This file is part of FLINT.

    FLINT is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    FLINT is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with FLINT; if not, write to the Free Software
    Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301 USA

=============================================================================*/
/******************************************************************************

    Copyright (C) 2012 William Hart

******************************************************************************/

#undef ulong /* prevent clash with stdlib */
#include <stdlib.h>
#define ulong unsigned long
#include <mpir.h>
#include "flint.h"
#include "ulong_extras.h"
#include "fmpz.h"
#include "qfb.h"

void qfb_reduce(qfb_t r, qfb_t f, fmpz_t D)
{
   int done = 0;
   fmpz_t t;

   fmpz_set(r->a, f->a);
   fmpz_set(r->b, f->b);
   fmpz_set(r->c, f->c);

   fmpz_init(t);

   while(!done)
   {
      done = 1;

      if (fmpz_cmp(r->c, r->a) < 0)
      {
         fmpz_swap(r->a, r->c);
         fmpz_neg(r->b, r->b);

         done = 0;
      }

      if (fmpz_cmpabs(r->b, r->a) > 0)
      {
         fmpz_add(t, r->a, r->a);
         fmpz_fdiv_r(r->b, r->b, t);
         if (fmpz_cmp(r->b, r->a) > 0)
            fmpz_sub(r->b, r->b, t);

         fmpz_add(t, t, t);
         fmpz_mul(r->c, r->b, r->b);
         fmpz_sub(r->c, r->c, D);
         fmpz_divexact(r->c, r->c, t);

         done = 0;
      }
   }

   if (fmpz_cmpabs(r->a, r->b) == 0 || fmpz_cmp(r->a, r->c) == 0)
      if (fmpz_sgn(r->b) < 0)
         fmpz_neg(r->b, r->b);

   fmpz_clear(t);
}
