macro LOG_MSG(msg) Z3_append_log(msg) end

"exit gracefully in case of error."
function exitf(x::ASCIIString)
  fprintf(STDERR,"BUG: %s.\n", message);
  exit(1);
end

"exit if unreachable code was reached"
function unreachable()
  error("unreachable code was reached")
end

"Simpler error handler"
function error_handler(ctx::Z3_context, e::Z3_error_code)
  printf("Error code: %d\n", e)
  error("incorrect use of Z3")
end

"""
Enable model construction. Other configuration parameters can be passed in the
cfg variable.  Also enable tracing to stderr and register custom error handler.
"""
function mk_context_custom(cfg::Z3_config, err::Z3_error_handler)
  Z3_set_param_value(cfg, "model", "true");
  ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, err);
  ctx
end

"""
Create a logical context.
Enable model construction only.
Also enable tracing to stderr and register standard error handler.
"""
function mk_context()
  cfg = Z3_mk_config()
  ctx = mk_context_custom(cfg, error_handler)
  Z3_del_config(cfg)
  ctx
end

"""
Create a logical context.

Enable fine-grained proof construction.
Enable model construction.

Also enable tracing to stderr and register standard error handler.
"""
function mk_proof_context()
  cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "proof", "true");
  ctx = mk_context_custom(cfg, throw_z3_error);
  Z3_del_config(cfg);
  ctx
end

"Create a variable using the given name and type"
function mk_var(ctx::Z3_context, name::ASCIIString, ty::Z3_sort)
  s::Z3_symbol = Z3_mk_string_symbol(ctx, name)
  Z3_mk_const(ctx, s, ty)
end

## Make variables
## ==============
"Create a boolean variable using the given name"
function mk_bool_var(ctx::Z3_context, name::ASCIIString)
  ty::Z3_sort = Z3_mk_bool_sort(ctx)
  mk_var(ctx, name, ty)
end

"Create an integer variable using the given name."
function mk_int_var(ctx::Z3_context, name::ASCIIString)
  ty::Z3_sort = Z3_mk_int_sort(ctx);
  return mk_var(ctx, name, ty);
end

"Create a real variable using the given name."
function mk_real_var(ctx::Z3_context, name::ASCIIString)
  ty::Z3_sort = Z3_mk_real_sort(ctx);
  return mk_var(ctx, name, ty);
end

"Create a Z3 integer node using a C int."
function mk_int(ctx::Z3_context, v::Cint)
  ty::Z3_sort = Z3_mk_int_sort(ctx);
  return Z3_mk_int(ctx, v, ty);
end

## Funciton application
## ====================
"Create the unary function application: <tt>(f x)</tt>."
function mk_unary_app(ctx::Z3_context, f::Z3_func_decl, x::Z3_ast)
  args[1] = Z3_ast[x];
  Z3_mk_app(ctx, f, Cint(1), args);
end

"Create the binary function application: <tt>(f x y)</tt>."
function mk_binary_app(ctx::Z3_context, f::Z3_func_decl, x::Z3_ast, y::Z3_ast)
  args[2] = Z3_ast[x, y];
  Z3_mk_app(ctx, f, Cint(2), args)
end

"""Check whether the logical context is satisfiable, and compare the result with
 the expected result. If the context is satisfiable, then display the model."""
function check(ctx::Z3_context, expected_result::Z3_lbool)
  local m::Z3_model;
  result = Z3_check_and_get_model(ctx, m);
  if result == Z3_L_FALSE
    @printf("unsat\n");
  elseif result == Z3_L_UNDEF
    @printf("unknown\n");
    @printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
  elseif result == Z3_L_TRUE
    @printf("sat\n%s\n", Z3_model_to_string(ctx, m));
  end

  Z3_del_model(ctx, m)
  if (result != expected_result)
    exitf("unexpected result");
  end
end


# """Prove that the constraints already asserted into the logical
# context implies the given formula.  The result of the proof is
# displayed.
#
# Z3 is a satisfiability checker. So, one can prove \c f by showing
# that <tt>(not f)</tt> is unsatisfiable.
# The context \c ctx is not modified by this function."""
# function prove(ctx::Z3_context, f::Z3_ast, is_valid::Z3_bool)
#   # save the current state of the context
#   Z3_push(ctx);
#
#   not_f = Z3_mk_not(ctx, f);
#   Z3_assert_cnstr(ctx, not_f);
#
#   m::Z3_model
#
#   result = Z3_check_and_get_model(ctx, m)
#
#   if result == Z3_L_FALSE:
#     #  /* proved */
#     @printf("valid\n");
#     if (!is_valid)
#       exitf("unexpected result");
#     end
#   elseif result == Z3_L_UNDEF
#     # /* Z3 failed to prove/disprove f. */
#     @printf("unknown\n");
#     if m != 0
#       # /* m should be viewed as a potential counterexample. */
#       @printf("potential counterexample:\n%s\n", Z3_model_to_string(ctx, m));
#     end
#     if is_valid
#       exitf("unexpected result");
#     end
#   elseif result == Z3_L_TRUE
#     # /* disproved */
#     @printf("invalid\n");
#     if (m)
#     # /* the model returned by Z3 is a counterexample */
#       printf("counterexample:\n%s\n", Z3_model_to_string(ctx, m));
#     end
#     if is_valid
#       exitf("unexpected result");
#     end
#   end
#
#   if m
#     Z3_del_model(ctx, m);
#   end
#   # /* restore context */
#   Z3_pop(ctx, 1);
# end
#
# """Assert the axiom: function f is injective in the i-th argument.
#
# The following axiom is asserted into the logical context:
#
# `forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i`
#
# Where, \c finv is a fresh function declaration."""
# function assert_inj_axiom(ctx::Z3_context, f::Z3_func_decl, i::Uint32)
#   unsigned sz, j;
#   Z3_sort finv_domain, finv_range;
#   Z3_func_decl finv;
#   Z3_sort * types; #types of the quantified variables */
#   Z3_symbol *   names; #names of the quantified variables */
#   Z3_ast * xs;         #arguments for the application f(x_0, ..., x_i, ..., x_{n-1}) */
#   Z3_ast   x_i, fxs, finv_fxs, eq;
#   Z3_pattern p;
#   Z3_ast   q;
#   sz = Z3_get_domain_size(ctx, f);
#
#   if i >= sz
#     exitf("failed to create inj axiom");
#   end
#
#   # declare the i-th inverse of f: finv
#   finv_domain = Z3_get_range(ctx, f);
#   finv_range  = Z3_get_domain(ctx, f, i);
#   finv        = Z3_mk_fresh_func_decl(ctx, "inv", 1, &finv_domain, finv_range);
#
#   # /* allocate temporary arrays */
#   types       = (Z3_sort *) malloc(sizeof(Z3_sort) * sz);
#   names       = (Z3_symbol *) malloc(sizeof(Z3_symbol) * sz);
#   xs          = (Z3_ast *) malloc(sizeof(Z3_ast) * sz);
#
#   # /* fill types, names and xs */
#   for (j = 0; j < sz; j++) { types[j] = Z3_get_domain(ctx, f, j); };
#   for (j = 0; j < sz; j++) { names[j] = Z3_mk_int_symbol(ctx, j); };
#   for (j = 0; j < sz; j++) { xs[j]    = Z3_mk_bound(ctx, j, types[j]); };
#
#   x_i = xs[i];
#
#   # /* create f(x_0, ..., x_i, ..., x_{n-1}) */
#   fxs         = Z3_mk_app(ctx, f, sz, xs);
#
#   # /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
#   finv_fxs    = mk_unary_app(ctx, finv, fxs);
#
#   # /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
#   eq          = Z3_mk_eq(ctx, finv_fxs, x_i);
#
#   # /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
#   p           = Z3_mk_pattern(ctx, 1, &fxs);
#   @printf("pattern: %s\n", Z3_pattern_to_string(ctx, p));
#   @printf("\n");
#
#   # /* create & assert quantifier */
#   q           = Z3_mk_forall(ctx,
#                                0, /* using default weight */
#                                1, /* number of patterns */
#                                &p, /* address of the "array" of patterns */
#                                sz, /* number of quantified variables */
#                                types,
#                                names,
#                                eq);
#   printf("assert axiom:\n%s\n", Z3_ast_to_string(ctx, q));
#   Z3_assert_cnstr(ctx, q);
#
#   # /* free temporary arrays */
#   free(types);
#   free(names);
#   free(xs);
# end
#
#
# """Assert the axiom: function f is commutative.
# This example uses the SMT-LIB parser to simplify the axiom construction."""
# function assert_comm_axiom(ctx::Z3_context, f::Z3_func_decl)
#   local t::Z3_sortt;
#   local f_name::Z3_symbol
#   local t_name::Z3_symbol
#   local q::Z3_ast ;
#
#   t = Z3_get_range(ctx, f);
#
#   if (Z3_get_domain_size(ctx, f) != 2 ||
#       Z3_get_domain(ctx, f, 0) != t ||
#       Z3_get_domain(ctx, f, 1) != t)
#       exitf("function must be binary, and argument types must be equal to return type");
#   end
#
#   # /* Inside the parser, function f will be referenced using the symbol 'f'. */
#   f_name = Z3_mk_string_symbol(ctx, "f");
#
#   # /* Inside the parser, type t will be referenced using the symbol 'T'. */
#   t_name = Z3_mk_string_symbol(ctx, "T");
#
#
#   Z3_parse_smtlib_string(ctx,
#                          "(benchmark comm :formula (forall (x T) (y T) (= (f x y) (f y x))))",
#                          1, &t_name, &t,
#                          1, &f_name, &f);
#   q = Z3_get_smtlib_formula(ctx, 0);
#   @printf("assert axiom:\n%s\n", Z3_ast_to_string(ctx, q));
#   Z3_assert_cnstr(ctx, q);
# end
#
# """Z3 does not support explicitly tuple updates. They can be easily implemented
# as macros. The argument \c t must have tuple type.
# A tuple update is a new tuple where field \c i has value \c new_val, and all
# other fields have the value of the respective field of \c t.
# <tt>update(t, i, new_val)</tt> is equivalent to
# <tt>mk_tuple(proj_0(t), ..., new_val, ..., proj_n(t))</tt>"""
# function mk_tuple_update(ctx::Z3_context, t::Z3_ast, i::Uint32, new_val::Z3_ast)
#     Z3_sort         ty;
#     Z3_func_decl   mk_tuple_decl;
#     unsigned            num_fields, j;
#     Z3_ast *            new_fields;
#     Z3_ast              result;
#
#     ty = Z3_get_sort(c, t);
#
#     if (Z3_get_sort_kind(c, ty) != Z3_DATATYPE_SORT)
#       exitf("argument must be a tuple");
#     end
#
#     num_fields = Z3_get_tuple_sort_num_fields(c, ty);
#
#     if (i >= num_fields)
#       exitf("invalid tuple update, index is too big");
#     end
#
#     new_fields = (Z3_ast*) malloc(sizeof(Z3_ast) * num_fields);
#     for j = 1:num_fields
#       if (i == j)
#         # /* use new_val at position i */
#         new_fields[j] = new_val;
#       else
#         # /* use field j of t */
#         Z3_func_decl proj_decl = Z3_get_tuple_sort_field_decl(c, ty, j);
#         new_fields[j] = mk_unary_app(c, proj_decl, t);
#       end
#     end
#     mk_tuple_decl = Z3_get_tuple_sort_mk_decl(c, ty);
#     result = Z3_mk_app(c, mk_tuple_decl, num_fields, new_fields);
#     free(new_fields);
#     return result;
# end
#
# ## Printing
# ## ========
#
# "Display a symbol in the given output stream"
# function display_symbol(c::Z3_context, FILE * out, Z3_symbol s)
#     switch (Z3_get_symbol_kind(c, s)) {
#     case Z3_INT_SYMBOL:
#         fprintf(out, "#%d", Z3_get_symbol_int(c, s));
#         break;
#     case Z3_STRING_SYMBOL:
#         fprintf(out, "%s", Z3_get_symbol_string(c, s));
#         break;
#     default:
#         unreachable();
#     }
# end
#
# "Display the given type"
# function display_sort(ctx::Z3_context, out::FILEPtr, ty::Z3_sort)
#     sort = Z3_get_sort_kind(c, ty)
#     if sort == Z3_UNINTERPRETED_SORT
#       display_symbol(c, out, Z3_get_sort_name(c, ty))
#     elseif sort == Z3_BOOL_SORT
#       fprintf(out, "bool");
#     elseif sort == Z3_INT_SORT
#       fprintf(out, "int");
#     elseif sort == Z3_REAL_SORT
#       fprintf(out, "real");
#     elseif sort == Z3_BV_SORT
#       fprintf(out, "bv%d", Z3_get_bv_sort_size(c, ty));
#     elseif sort == Z3_ARRAY_SORT
#         fprintf(out, "[");
#         display_sort(c, out, Z3_get_array_sort_domain(c, ty));
#         fprintf(out, "->");
#         display_sort(c, out, Z3_get_array_sort_range(c, ty));
#         fprintf(out, "]");
#     elseif sort == Z3_DATATYPE_SORT
#   		if Z3_get_datatype_sort_num_constructors(c, ty) != 1
#   			fprintf(out, "%s", Z3_sort_to_string(c,ty
#       end
#       num_fields::Uint32 = Z3_get_tuple_sort_num_fields(c, ty);
#       fprintf(out, "(");
#       for i = 1:num_fields
#         Z3_func_decl field = Z3_get_tuple_sort_field_decl(c, ty, i);
#         if i > 0
#           fprintf(out, ", ");
#         end
#         display_sort(c, out, Z3_get_range(c, field));
#       end
#       fprintf(out, ")");
#     else
#       fprintf(out, "unknown[");
#       display_symbol(c, out, Z3_get_sort_name(c, ty));
#       fprintf(out, "]");
#     end
# end
#
# """Custom ast pretty printer
# This function demonstrates how to use the API to navigate terms"""
# function display_ast(c::Z3_context, FILE * out, Z3_ast v)
#     ast_kind == Z3_get_ast_kind(c, v)
#     if ast_kind == Z3_NUMERAL_AST
#       local t::Z3_sort
#       fprintf(out, "%s", Z3_get_numeral_string(c, v));
#       t = Z3_get_sort(c, v);
#       fprintf(out, ":");
#       display_sort(c, out, t);
#     elseif ast_kind == Z3_APP_AST
#       app::Z3_app = Z3_to_app(c, v);
#       num_fields::Uint32 = Z3_get_app_num_args(c, app);
#       d::Z3_func_decl = Z3_get_app_decl(c, app);
#       fprintf(out, "%s", Z3_func_decl_to_string(c, d));
#       if (num_fields > 0)
#         fprintf(out, "[");
#         for i = 0:num_fields
#           if (i > 0)
#             fprintf(out, ", ");
#           end
#           display_ast(c, out, Z3_get_app_arg(c, app, i));
#         end
#           fprintf(out, "]");
#       end
#     elseif ast_kind == Z3_QUANTIFIER_AST
#       fprintf(out, "quantifier");
#     else
#       fprintf(out, "#unknown");
#     end
# end

# "Custom function interpretations pretty printer."
# void display_function_interpretations(c::Z3_context, FILE * out, Z3_model m)
# {
#     unsigned num_functions, i;
#
#     fprintf(out, "function interpretations:\n");
#
#     num_functions = Z3_get_model_num_funcs(c, m);
#     for (i = 0; i < num_functions; i++) {
#         Z3_func_decl fdecl;
#         Z3_symbol name;
#         Z3_ast func_else;
#         unsigned num_entries, j;
#
#         fdecl = Z3_get_model_func_decl(c, m, i);
#         name = Z3_get_decl_name(c, fdecl);
#         display_symbol(c, out, name);
#         fprintf(out, " = {");
#         num_entries = Z3_get_model_func_num_entries(c, m, i);
#         for (j = 0; j < num_entries; j++) {
#             unsigned num_args, k;
#             if (j > 0) {
#                 fprintf(out, ", ");
#             }
#             num_args = Z3_get_model_func_entry_num_args(c, m, i, j);
#             fprintf(out, "(");
#             for (k = 0; k < num_args; k++) {
#                 if (k > 0) {
#                     fprintf(out, ", ");
#                 }
#                 display_ast(c, out, Z3_get_model_func_entry_arg(c, m, i, j, k));
#             }
#             fprintf(out, "|->");
#             display_ast(c, out, Z3_get_model_func_entry_value(c, m, i, j));
#             fprintf(out, ")");
#         }
#         if (num_entries > 0) {
#             fprintf(out, ", ");
#         }
#         fprintf(out, "(else|->");
#         func_else = Z3_get_model_func_else(c, m, i);
#         display_ast(c, out, func_else);
#         fprintf(out, ")}\n");
#     }
# }

# /**
#    \brief Custom model pretty printer.
# */
# void display_model(c::Z3_context, FILE * out, Z3_model m)
# {
#     unsigned num_constants;
#     unsigned i;
#
#     num_constants = Z3_get_model_num_constants(c, m);
#     for (i = 0; i < num_constants; i++) {
#         Z3_symbol name;
#         Z3_func_decl cnst = Z3_get_model_constant(c, m, i);
#         Z3_ast a, v;
#         Z3_bool ok;
#         name = Z3_get_decl_name(c, cnst);
#         display_symbol(c, out, name);
#         fprintf(out, " = ");
#         a = Z3_mk_app(c, cnst, 0, 0);
#         v = a;
#         ok = Z3_eval(c, m, a, &v);
#         display_ast(c, out, v);
#         fprintf(out, "\n");
#     }
#     display_function_interpretations(c, out, m);
# }

# /**
#    \brief Similar to #check, but uses #display_model instead of #Z3_model_to_string.
# */
# void check2(ctx::Z3_context, Z3_lbool expected_result)
# {
#     Z3_model m      = 0;
#     Z3_lbool result = Z3_check_and_get_model(ctx, &m);
#     switch (result) {
#     case Z3_L_FALSE:
#         printf("unsat\n");
#         break;
#     case Z3_L_UNDEF:
#         printf("unknown\n");
#         printf("potential model:\n");
#         display_model(ctx, stdout, m);
#         break;
#     case Z3_L_TRUE:
#         printf("sat\n");
#         display_model(ctx, stdout, m);
#         break;
#     }
#     if (m) {
#         Z3_del_model(ctx, m);
#     }
#     if (result != expected_result) {
#         exitf("unexpected result");
#     }
# }

"Display Z3 version in the standard output."
function display_version()
  major = Ref{Cuint}(0)
  minor = Ref{Cuint}(0)
  build = Ref{Cuint}(0)
  revision = Ref{Cuint}(0)

  Z3_get_version(major, minor, build, revision)
  println("Z3 $(major.x).$(minor.x).$(build.x).$(revision.x)");
end
