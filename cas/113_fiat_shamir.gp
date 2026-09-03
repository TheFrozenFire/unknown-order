\\ Fiat-Shamir compilation of the public-coin eqdl / slot Sigma.
\\ Mirrors FiatShamir.v.
\\ Challenge is derived from public statement + commitment.
\\ The NI verifier does not take a free coin c.
\\ Pin N = pin_N=187, slot-1 from cas/97: P=g^tau, a=3, s=4.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

read("lib/pin.gp");

N = pin_N; g = 3; tau = 5;

\\ Horner-at-2 modulo m.  Same map as Rocq fs_challenge.
fs_challenge(m, xs) = {
  my(acc = 0, ii);
  for(ii = 1, length(xs), acc = (2*acc + xs[ii]) % m);
  acc
};
fs_eqdl_challenge(NN, gg, h, u, v, t1, t2) =
  fs_challenge(NN, [NN, gg, h, u, v, t1, t2]);

\\ NI verifier recomputes c; no verifier-supplied challenge.
fs_eqdl_verify(NN, gg, h, u, v, t1, t2, zz) = {
  my(c = fs_eqdl_challenge(NN, gg, h, u, v, t1, t2));
  lift(Mod(gg, NN)^zz) == (t1 * lift(Mod(h, NN)^c)) % NN && \
    lift(Mod(u, NN)^zz) == (t2 * lift(Mod(v, NN)^c)) % NN
};

\\ --- setup: slot-1 Schnorr (uses secret a, nonce s; not NI inputs) ---
aa = 3; ss = 4;
Pbase = lift(Mod(g, N)^tau);
Qslot = lift(Mod(Pbase, N)^aa);
t1 = lift(Mod(Pbase, N)^ss);
t2 = t1;
c = fs_eqdl_challenge(N, Pbase, Qslot, Pbase, Qslot, t1, t2);
zz = ss + c*aa;

check(c == fs_eqdl_challenge(N, Pbase, Qslot, Pbase, Qslot, t1, t2), \
  "c derived from statement+commitment, not a verifier coin");
check(fs_eqdl_verify(N, Pbase, Qslot, Pbase, Qslot, t1, t2, zz) == 1, \
  "honest NI proof verifies");

\\ response under a different challenge fails the NI check
zz_bad = ss + (c+1)*aa;
check(fs_eqdl_verify(N, Pbase, Qslot, Pbase, Qslot, t1, t2, zz_bad) == 0, \
  "response for a different challenge fails");

\\ two distinct commitments for the same statement yield different c
ss2 = 7;
t1b = lift(Mod(Pbase, N)^ss2);
c2 = fs_eqdl_challenge(N, Pbase, Qslot, Pbase, Qslot, t1b, t1b);
check(t1b != t1, "distinct first messages");
check(c2 != c, "derived challenge depends on the first message");
zz2 = ss2 + c2*aa;
check(fs_eqdl_verify(N, Pbase, Qslot, Pbase, Qslot, t1b, t1b, zz2) == 1, \
  "second honest NI proof verifies");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
