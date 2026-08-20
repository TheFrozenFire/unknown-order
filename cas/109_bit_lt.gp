\\ Bit less-than.  Mirrors BitLt.v.

ok = 0; fail = 0;
check(cond, name) = if(cond, ok++; printf("  ok  %s\n", name), fail++; printf(" FAIL %s\n", name));

lt(x,y) = (1-x)*y;
check(lt(0,1)==1, "0<1");
check(lt(1,0)==0, "1 not< 0");
check(lt(0,0)==0 && lt(1,1)==0, "equal not <");
check(lt(0,1)==1-0*1, "y - x y");

printf("%d ok, %d fail\n", ok, fail);
if(fail, error("CAS failures"));
