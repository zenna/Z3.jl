using Z3

@printf("\nfind_model_example2\n");

ctx        = mk_context();
x          = Var(Integer, ctx=ctx, name="x");
y          = Var(Integer, ctx=ctx, name="y");
one        = mk_int(ctx, Int32(1));
two        = mk_int(ctx, Int32(2));

args       = [y,one]

y_plus_one = mk_add(ctx, 2, args);

c1         = mk_lt(ctx, x, y_plus_one);
c2         = mk_gt(ctx, x, two);

assert_cnstr(ctx, c1);
assert_cnstr(ctx, c2);

@printf("model for: x < y + 1, x > 2\n");
check(ctx, L_TRUE);

# /* assert not(x = y) */
x_eq_y     = mk_eq(ctx, x, y);
c3         = mk_not(ctx, x_eq_y);
assert_cnstr(ctx, c3);

@printf("model for: x < y + 1, x > 2, not(x = y)\n");
check(ctx, Z3.Z3_L_TRUE);

del_context(ctx);
