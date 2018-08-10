/*
    Copyright (C) 2014 Alex J. Best

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <http://www.gnu.org/licenses/>.
*/

#include "fmpz_mat.h"

slong
_conditioning(fmpz_mat_t T, slong row, slong col1)
{
    slong row1 = row + 1;
    slong col2 = -1;
    slong colsT = T->c;
    slong rowsT = T->r;
    slong c, i, j;
    fmpz_t t1, t2, t, g, q1, r1, q2, r2 ,q, n, nn;

    fmpz_init(t1);
    fmpz_init(t2);
    fmpz_init(t);
    fmpz_init(g);
    fmpz_init(q1);
    fmpz_init(r1);
    fmpz_init(q2);
    fmpz_init(r2);
    fmpz_init(q);
    fmpz_init(n);
    fmpz_init(nn);

    row1 = row + 1;

    for (c = col1 + 1; c < colsT; c++)
    {
        for (i = row1; i < rowsT; i++)
        {
            fmpz_mul(t1, fmpz_mat_entry(T, row, col1), fmpz_mat_entry(T, i, c));
            fmpz_mul(t2, fmpz_mat_entry(T, row, c), fmpz_mat_entry(T, i, col1));
            if (!fmpz_equal(t1, t2))
            {
                col2 = c;
                if (i != row1)
                {
                    for (j = col1; j < colsT; j++)
                    {
                        fmpz_add(fmpz_mat_entry(T, row1, j), fmpz_mat_entry(T, row1, j), fmpz_mat_entry(T, i, j));
                    }
                }
                break;
            }
        }
        if (col2 != -1)
        {
            break;
        }
    }

    if (row1 == rowsT - 1)
    {
        fmpz_clear(t1);
        fmpz_clear(t2);
        fmpz_clear(t);
        fmpz_clear(g);
        fmpz_clear(q1);
        fmpz_clear(r1);
        fmpz_clear(q2);
        fmpz_clear(r2);
        fmpz_clear(q);
        fmpz_clear(n);
        fmpz_clear(nn);

        return col2;
    }
    
    for (i = row + 2; i < rowsT; i++)
    {
        fmpz_gcd(g, fmpz_mat_entry(T, row1, col1), fmpz_mat_entry(T, i, col1));
        if (fmpz_is_zero(g))
        {
            continue;
        }

        fmpz_divexact(q, fmpz_mat_entry(T, row1, col1), g);
        fmpz_tdiv_qr(q1, r1, q, fmpz_mat_entry(T, row, col1));

        if (fmpz_sgn(r1) == -1)
        {
            fmpz_add(r1, r1, fmpz_mat_entry(T, row, col1));
            fmpz_sub_ui(q1, q1, -1);
        }

        fmpz_divexact(q, fmpz_mat_entry(T, i, col1), g);
        fmpz_tdiv_qr(q2, r2, q, fmpz_mat_entry(T, row, col1));
        if (fmpz_sgn(r1) == -1)
        {
            fmpz_add(r2, r2, fmpz_mat_entry(T, row, col1));
            fmpz_sub_ui(q2, q2, -1);
        }
        fmpz_mul(t1, fmpz_mat_entry(T, row, col1), fmpz_mat_entry(T, i, col2));
        fmpz_mul(t2, fmpz_mat_entry(T, row, col2), fmpz_mat_entry(T, i, col1));
        if (!fmpz_equal(t1, t2))
        {
            fmpz_sub(n, t1, t2);
            fmpz_mul(t1, fmpz_mat_entry(T, row, col1), fmpz_mat_entry(T, row1, col2));
            fmpz_mul(t2, fmpz_mat_entry(T, row, col2), fmpz_mat_entry(T, row1, col1));
            fmpz_sub(nn, t2, t1);
            if (fmpz_sgn(n) == fmpz_sgn(nn) && fmpz_divisible(nn, n))
            {
                fmpz_neg(r2, r2);
            }
        }
        fmpz_zero(t1);
        fmpz_set(t2, r1);
        fmpz_gcd(g, t2, fmpz_mat_entry(T, row, col1));

        while (!fmpz_is_one(g))
        {
            fmpz_add(t2, t2, r2);
            fmpz_add_ui(t1, t1, 1);
            fmpz_gcd(g, t2, fmpz_mat_entry(T, row, col1));
        }
        if (!fmpz_is_zero(t1))
        {
            if (fmpz_sgn(r2) == -1)
            {
                fmpz_neg(t1, t1);
            }
            for (j = col1; j < colsT - 1; j++)
            {
                fmpz_mul(t, fmpz_mat_entry(T, i, j), t1);
                fmpz_add(fmpz_mat_entry(T, row1, j), fmpz_mat_entry(T, row1, j), t);
            }
        }
    }

    fmpz_clear(t1);
    fmpz_clear(t2);
    fmpz_clear(t);
    fmpz_clear(g);
    fmpz_clear(q1);
    fmpz_clear(r1);
    fmpz_clear(q2);
    fmpz_clear(r2);
    fmpz_clear(q);
    fmpz_clear(n);
    fmpz_clear(nn);

    return col2;
}

void
_column_reduction(fmpz_mat_t T, slong row, slong col1, slong col2)
{
    slong row1 = row + 1;
    slong col11 = col1 + 1;
    slong n = T->c - 1;
    slong rowsT = T->r;

    slong i, j;

    fmpz_t t, t1, t2, g, a, b, q, c, d;

    fmpz_init(t);
    fmpz_init(t1);
    fmpz_init(t2);
    fmpz_init(g);
    fmpz_init(a);
    fmpz_init(b);
    fmpz_init(q);
    fmpz_init(c);
    fmpz_init(d);

    for (i = row1; i < rowsT; i++)
    {
        if (i == row1 || !fmpz_is_zero(fmpz_mat_entry(T, i, col1)))
        {
            fmpz_xgcd(g, a, b, fmpz_mat_entry(T, row, col1), fmpz_mat_entry(T, i, col1));
            fmpz_divexact(c, fmpz_mat_entry(T, row, col1), g);
            fmpz_divexact(d, fmpz_mat_entry(T, i, col1), g);
            fmpz_neg(d, d);
            if (i == row1)
            {
                fmpz_mul(t1, d, fmpz_mat_entry(T, row, col2));
                fmpz_mul(t2, c, fmpz_mat_entry(T, row1, col2));
                fmpz_add(t, t1, t2);
                if (fmpz_sgn(t) == -1)
                {
                    fmpz_neg(c, c);
                    fmpz_neg(d, d);
                }
            }
            fmpz_set(fmpz_mat_entry(T, row, col1), g);
            fmpz_zero(fmpz_mat_entry(T, i, col1));
            for (j = col11; j < n; j++)
            {
                fmpz_set(t, fmpz_mat_entry(T, row, j));
                fmpz_mul(t1, fmpz_mat_entry(T, row, j), a);
                fmpz_mul(t2, fmpz_mat_entry(T, i, j), b);
                fmpz_add(fmpz_mat_entry(T, row, j), t1, t2);
                fmpz_mul(t1, fmpz_mat_entry(T, i, j), c);
                fmpz_mul(t2, t, d);
                fmpz_add(fmpz_mat_entry(T, i, j), t1, t2);
            }
        }
    }
    for (i = row + 2; i < rowsT; i++)
    {
        if (fmpz_sgn(fmpz_mat_entry(T, i, col2)) == -1 || fmpz_cmp(fmpz_mat_entry(T, i, col2), fmpz_mat_entry(T, row1, col2)) >= 0)
        {
            fmpz_fdiv_q(q, fmpz_mat_entry(T, i ,col2), fmpz_mat_entry(T, row1, col2));
            fmpz_neg(q, q);
            for (j = col11; j < n; j++)
            {
                fmpz_mul(t, q, fmpz_mat_entry(T, row1, j));
                fmpz_add(fmpz_mat_entry(T, i, j), fmpz_mat_entry(T, i, j), t);
            }
        }
    }
    for (i = 0; i <= row - 1; i++)
    {
         if (fmpz_sgn(fmpz_mat_entry(T, i, col1)) == -1 || fmpz_cmp(fmpz_mat_entry(T, i, col1), fmpz_mat_entry(T, row, col1)) >= 0)
         {
            fmpz_fdiv_q(q, fmpz_mat_entry(T, i ,col1), fmpz_mat_entry(T, row, col1));
            fmpz_neg(q, q);
            for (j = col1; j < n; j++)
            {
                fmpz_mul(t, q, fmpz_mat_entry(T, row, j));
                fmpz_add(fmpz_mat_entry(T, i, j), fmpz_mat_entry(T, i, j), t);
            }
        }
    }

    for (i = 0; i <= row; i++)
    {
         if (fmpz_sgn(fmpz_mat_entry(T, i, col2)) == -1 || fmpz_cmp(fmpz_mat_entry(T, i, col2), fmpz_mat_entry(T, row1, col2)) >= 0)
        {
            fmpz_fdiv_q(q, fmpz_mat_entry(T, i ,col2), fmpz_mat_entry(T, row1, col2));
            fmpz_neg(q, q);
            for (j = col11; j < n; j++)
            {
                fmpz_mul(t, q, fmpz_mat_entry(T, row1, j));
                fmpz_add(fmpz_mat_entry(T, i, j), fmpz_mat_entry(T, i, j), t);
            }
        }
    }
    fmpz_clear(t);
    fmpz_clear(t1);
    fmpz_clear(t2);
    fmpz_clear(g);
    fmpz_clear(a);
    fmpz_clear(b);
    fmpz_clear(q);
    fmpz_clear(c);
    fmpz_clear(d);
}

void
fmpz_mat_hnf_storjohann(fmpz_mat_t H, const fmpz_mat_t A)
{
  fmpz_mat_t T;
  slong n, m, n1, m1, col1, col2, row, i, j;

  fmpz_mat_init(T, A->r + 2, A->c + 2);
  
  fmpz_one(fmpz_mat_entry(T, 0, 0));
  fmpz_one(fmpz_mat_entry(T, A->r + 1, A->c + 1));

  n = T->r;
  m = T->c;
  n1 = n - 1;
  m1 = m - 1;

  for (i = 1; i < n1; i++)
  {
      for (j = 1; j < m1; j++)
      {
          fmpz_set(fmpz_mat_entry(T, i, j), fmpz_mat_entry(A, i - 1, j - 1));
      }
  }

  col1 = 0;
  col2 = -1;
  row = 0;

  while (col2 < m - 1)
  {
      col2 = _conditioning(T, row, col1);
      _column_reduction(T, row, col1, col2);
      col1 = col2;
      row = row + 1;
  }

  for (i = 1; i < n1; i++)
  {
      for (j = 1; j < m1; j++)
      {
          fmpz_set(fmpz_mat_entry(H, i - 1, j - 1), fmpz_mat_entry(T, i, j));
      }
  }

  fmpz_mat_clear(T);

  return;
}
