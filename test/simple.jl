using Z3

Z3_context ctx;
ctx = mk_context();
# /* do something with the context */
println("CONTEXT:\n$(context_to_string(ctx)) END OF CONTEXT")
del_context(ctx)
