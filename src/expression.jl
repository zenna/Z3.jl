##  AST
## ====
# abstract syntax tree node. That is, the data-structure used in Z3 to represent
# terms, formulas and types.

# typealias MathNumber Union(Real, Integer, Bool)

# The different kinds of Z3 AST (abstract syntax trees). That is, terms, formulas and types.
#
# Z3_APP_AST: constant and applications
# Z3_NUMERAL_AST: numeral constants
# Z3_VAR_AST: bound variables
# Z3_QUANTIFIER_AST: quantifiers
# Z3_SORT_AST: sort
# Z3_FUNC_DECL_AST: function declaration
# Z3_UNKNOWN_AST: internal

# AbstractAst = Union(Ast, Ex)
#
# # AST = Union(Ast, Ex)
# "Convenience type representing a variable"
# type Ex{T <: MathNumber} <: Real
#   ptr::Ptr{Void}
# end

function Var{T<: MathNumber}(::Type{T};
                          name::ASCIIString = genvar(),
                          ctx::Context = global_context())
  # safe_add!(name, ctx)
  Ex{T}(mk_var(T, ctx, name))
end

## Constructing Sorts
## =================
mk_sort(::Type{Bool}) = mk_bool_sort
mk_sort(::Type{Real}) = mk_real_sort
mk_sort(::Type{Integer}) = mk_int_sort

## Make variables
## ==============
"Create a variable using the given name and type"
function mk_var(ctx::Context, name::ASCIIString, ty::Sort)
  s::Z3Symbol = mk_string_symbol(ctx, name)
  return mk_const(ctx, s, ty)
end

"Create a variable using the given name"
function mk_var{T <: MathNumber}(::Type{T}, ctx::Context, name::ASCIIString)
  ty::Sort = mk_sort(T)(ctx)
  mk_var(ctx, name, ty)
end

# ## Make Numerals
# ## =============
# "Create a Z3 integer node using a C int."
# function mk_int(ctx::Context, v::Cint)
#   ty::Z3_sort = Z3_mk_int_sort(ctx);
#   return Z3_mk_int(ctx, v, ty);
# end

## Arithmetic
# ## ==========
# boolop2opensmt = @compat Dict(:(>=) => opensmt_mk_geq, :(>) => opensmt_mk_gt,
#                               :(<=) => opensmt_mk_leq, :(<) => opensmt_mk_lt,
#                               :(==) => opensmt_mk_eq)
#
# ## Real × Real -> Bool
# for (op,opensmt_func) in boolop2opensmt
#   @eval ($op){T1<:Real, T2<:Real}(ctx::Context, x::Ex{T1}, y::Ex{T2}) =
#     Ex{Bool}($opensmt_func(ctx.ctx,x.e,y.e), union(x.vars,y.vars))
#   # Var and constant c
#   @eval ($op){T1<:Real, T2<:Real}(ctx::Context, x::Ex{T1}, c::T2) =
#     Ex{Bool}($opensmt_func(ctx.ctx,x.e,convert(ctx, Ex{promote_type(T1,T2)},c).e), x.vars)
#
#   # constant c and Var
#   @eval ($op){T1<:Real, T2<:Real}(ctx::Context, c::T1, x::Ex{T2}) =
#     Ex{Bool}($opensmt_func(ctx.ctx,convert(ctx, Ex{promote_type(T1,T2)},c).e, x.e),x.vars)
#
#   # Default Contex
#   @eval ($op){T1<:Real, T2<:Real}(x::Ex{T1}, y::Ex{T2}) = ($op)(global_context(), x, y)
#   @eval ($op){T1<:Real, T2<:Real}(x::Ex{T1}, c::T2) = ($op)(global_context(), x, c)
#   @eval ($op){T1<:Real, T2<:Real}(c::T1, x::Ex{T2}) = ($op)(global_context(), c, x)
# end
