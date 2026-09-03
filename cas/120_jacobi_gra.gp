\\ Jager-Schwenk: Jacobi is standard-easy and not a ring polynomial.
\\ Mirrors JagerSchwenk.v.
\\ GRA-hard  =/=>  standard-model hard.  AM09 remains in-model.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

p = pin_p; q = pin_q; N = pin_N;

jN(a) = kronecker(a, N);

check(jN(1) == 1,                       "(1/N)=1");
check(jN(2) == kronecker(2,p)*kronecker(2,q), "(2/N)=(2/p)(2/q)");
check(jN(2) != jN(1),                   "Jacobi takes two values: not a constant polynomial");

\\ two units of opposite Jacobi
check(gcd(2,N)==1 && gcd(1,N)==1,       "1 and 2 are units");
check(jN(2) == -1,                      "(2/187)=-1");
check(jN(3) == kronecker(3,p)*kronecker(3,q), "(3/N) well-defined");

\\ a degree-<=2 interpolant through (1,j(1)), (2,j(2)), (5,j(5))
\\ fails at 3.  Fit in Q via Lagrange on three x-values.
xs = [1,2,5];
ys = [jN(1), jN(2), jN(5)];
\\ unique deg<=2 poly.  Evaluate at 3.
lagrange(x) = {
  my(s = 0, jj, kk, num, den);
  for(jj = 1, 3, \
    num = 1; den = 1; \
    for(kk = 1, 3, \
      if(kk != jj, num *= (x - xs[kk]); den *= (xs[jj] - xs[kk])) \
    ); \
    s += ys[jj] * num / den \
  );
  s
};
check(lagrange(1) == ys[1],             "fit at 1");
check(lagrange(2) == ys[2],             "fit at 2");
check(lagrange(5) == ys[3],             "fit at 5");
check(lagrange(3) == -2,                "fit at 3 is -2, not Jacobi");
j3 = jN(3);
l3 = lagrange(3);
check(l3 != j3,                         "deg<=2 interpolant misses Jacobi at 3");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
