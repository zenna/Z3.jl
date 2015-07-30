using Z3
using Base.Test

@printf("\nfind_model_example1\n")

ctx     = mk_context();

x       = Var(Bool; ctx = ctx, name = "x")
y       = Var(Bool; ctx = ctx, name = "y")

x_xor_y = mk_xor(ctx, x, y)

assert_cnstr(ctx, x_xor_y)

@printf("model for: x xor y\n")
@test check(ctx, Z3_L_TRUE) == Z3.Z3_L_TRUE

del_context(ctx);
