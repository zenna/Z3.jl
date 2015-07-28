using Z3
# Demonstration of how Z3 can be used to prove validity of
# De Morgan's Duality Law: {e not(x and y) <-> (not x) or ( not y) }

cfg                = mk_config();
ctx                = mk_context(cfg);
del_config(cfg);
bool_sort          = mk_bool_sort(ctx);
symbol_x           = mk_int_symbol(ctx, Int32(0));
symbol_y           = mk_int_symbol(ctx, Int32(1));
x                  = mk_const(ctx, symbol_x, bool_sort);
y                  = mk_const(ctx, symbol_y, bool_sort);

# /* De Morgan - with a negation around */
# /* !(!(x && y) <-> (!x || !y)) */
not_x              = mk_not(ctx, x);
not_y              = mk_not(ctx, y);
args               = [x,y]
x_and_y            = mk_and(ctx, UInt32(2), args);
ls                 = mk_not(ctx, x_and_y);
args               = [not_x, not_y]
rs                 = mk_or(ctx, UInt32(2), args);
conjecture         = mk_iff(ctx, ls, rs);
negated_conjecture = mk_not(ctx, conjecture);

assert_cnstr(ctx, negated_conjecture)

result = check(ctx)
if result == Z3.Z3_L_FALSE
    # /* The negated conjecture was unsatisfiable, hence the conjecture is valid */
    println("DeMorgan is valid");
elseif result == Z3.Z3_L_UNDEF
    # /* Check returned undef */
    println("Undef");
elseif result == Z3.Z3_L_TRUE
    # /* The negated conjecture was satisfiable, hence the conjecture is not valid */
    println("DeMorgan is not valid");
else
  @show typeof(result)
  println("error", result)
end
del_context(ctx);
