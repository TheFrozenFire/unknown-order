\\ Bit AND/OR/XOR.  Mirrors BitLogic.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

andp(x,y) = x*y;
orp(x,y) = x+y-x*y;
xorp(x,y) = x+y-2*x*y;

oktab = 1;
for(x = 0, 1, for(y = 0, 1, \
  if(andp(x,y) != bitand(x,y), oktab = 0); \
  if(orp(x,y) != bitor(x,y), oktab = 0); \
  if(xorp(x,y) != bitxor(x,y), oktab = 0) \
));
check(oktab, "AND/OR/XOR match bitand/bitor/bitxor");
check(andp(1,1)==1 && andp(1,0)==0, "AND table");
check(orp(0,0)==0 && orp(1,0)==1 && orp(1,1)==1, "OR table");
check(xorp(0,0)==0 && xorp(1,0)==1 && xorp(1,1)==0, "XOR table");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
