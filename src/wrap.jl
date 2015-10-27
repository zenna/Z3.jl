typealias Z3_symbol Ptr{Void}
typealias Z3_literals Ptr{Void}
typealias Z3_theory Ptr{Void}
typealias Z3_config Ptr{Void}
typealias Z3_context Ptr{Void}
typealias Z3_sort Ptr{Void}
typealias Z3_func_decl Ptr{Void}
typealias Z3_ast Ptr{Void}
typealias Z3_app Ptr{Void}
typealias Z3_pattern Ptr{Void}
typealias Z3_model Ptr{Void}
typealias Z3_constructor Ptr{Void}
typealias Z3_constructor_list Ptr{Void}
typealias Z3_params Ptr{Void}
typealias Z3_param_descrs Ptr{Void}
typealias Z3_goal Ptr{Void}
typealias Z3_tactic Ptr{Void}
typealias Z3_probe Ptr{Void}
typealias Z3_stats Ptr{Void}
typealias Z3_solver Ptr{Void}
typealias Z3_ast_vector Ptr{Void}
typealias Z3_ast_map Ptr{Void}
typealias Z3_apply_result Ptr{Void}
typealias Z3_func_interp Ptr{Void}
typealias Z3_func_entry Ptr{Void}
typealias Z3_fixedpoint Ptr{Void}
typealias Z3_rcf_num Ptr{Void}
typealias Z3_theory_data Ptr{Void} #Is actually a void ptr

## Function Typedefs
typealias Z3_reduce_eq_callback_fptr Ptr{Void}
typealias Z3_reduce_app_callback_fptr Ptr{Void}
typealias Z3_reduce_distinct_callback_fptr Ptr{Void}
typealias Z3_theory_callback_fptr Ptr{Void}
typealias Z3_theory_final_check_callback_fptr Ptr{Void}
typealias Z3_theory_ast_bool_callback_fptr Ptr{Void}
typealias Z3_theory_ast_ast_callback_fptr Ptr{Void}
typealias Z3_theory_ast_callback_fptr Ptr{Void}

# FIXME: Handle error handlers correctly
typealias Z3_error_handler Ptr{Void}

typealias Z3_fixedpoint_reduce_assign_callback_fptr Ptr{Void}
typealias Z3_fixedpoint_reduce_app_callback_fptr Ptr{Void}

typealias Z3_string Ptr{UInt8}
typealias Z3_string_ptr Ptr{Ptr{UInt8}}
typealias Z3_bool Cint
typealias Z3Bool Cint


## Wrapper Julia types
## ===================

## Pointer Types
typealias Z3SymbolPtr Ptr{Void}
typealias LiteralsPtr Ptr{Void}
typealias TheoryPtr Ptr{Void}
typealias ConfigPtr Ptr{Void}
typealias ContextPtr Ptr{Void}
typealias SortPtr Ptr{Void}
typealias FuncDeclPtr Ptr{Void}
typealias AstPtr Ptr{Void}
typealias AppPtr Ptr{Void}
typealias PatternPtr Ptr{Void}
typealias ModelPtr Ptr{Void}
typealias ConstructorPtr Ptr{Void}
typealias ConstructorListPtr Ptr{Void}
typealias ParamsPtr Ptr{Void}
typealias ParamDescrsPtr Ptr{Void}
typealias GoalPtr Ptr{Void}
typealias TacticPtr Ptr{Void}
typealias ProbePtr Ptr{Void}
typealias StatsPtr Ptr{Void}
typealias SolverPtr Ptr{Void}
typealias AstVectorPtr Ptr{Void}
typealias AstMapPtr Ptr{Void}
typealias ApplyResultPtr Ptr{Void}
typealias FuncInterpPtr Ptr{Void}
typealias FuncEntryPtr Ptr{Void}
typealias FixedpointPtr Ptr{Void}
typealias RcfNumPtr Ptr{Void}
typealias TheoryDataPtr Ptr{Void}
typealias ReduceEqCallbackFptrPtr Ptr{Void}
typealias ReduceAppCallbackFptrPtr Ptr{Void}
typealias ReduceDistinctCallbackFptrPtr Ptr{Void}
typealias TheoryCallbackFptrPtr Ptr{Void}
typealias TheoryFinalCheckCallbackFptrPtr Ptr{Void}
typealias TheoryAstBoolCallbackFptrPtr Ptr{Void}
typealias TheoryAstAstCallbackFptrPtr Ptr{Void}
typealias TheoryAstCallbackFptrPtr Ptr{Void}
typealias FixedpointReduceAssignCallbackFptrPtr Ptr{Void}
typealias FixedpointReduceAppCallbackFptrPtr Ptr{Void}

## Types from Z3
## =============

abstract Z3CType

# Sort types
abstract Sort <: Z3CType
convert(::Type{Sort}, x::Ptr{Void}) = UnknownSort(x)
type UnknownSort <: Sort ptr::SortPtr end
type UninterpretedSort <: Sort ptr::SortPtr end
type BoolSort <: Sort ptr::SortPtr end
type IntSort <: Sort ptr::SortPtr end
type RealSort <: Sort ptr::SortPtr end
type BitVectorSort{S} <: Sort ptr::SortPtr end
type FiniteDomainSort <: Sort ptr::SortPtr end
type ArraySort <: Sort ptr::SortPtr end
type TupleSort <: Sort ptr::SortPtr end
type EnumerationSort <: Sort ptr::SortPtr end
type ListSort <: Sort ptr::SortPtr end

type Z3Symbol <: Z3CType ptr::Z3SymbolPtr end
type Literals <: Z3CType ptr::LiteralsPtr end
type Theory <: Z3CType ptr::TheoryPtr end
type Config <: Z3CType ptr::ConfigPtr end
type Context <: Z3CType ptr::ContextPtr end
type FuncDecl <: Z3CType ptr::FuncDeclPtr end

## Ast types
# The issues with ASTS:
# We want ASTs to be interoperable with existing functions, such that
# if someone has written f(x::Number) they can use f with a variable of numerical type
# OTOH we like f(x::ArrayAst) to cause an error

# On the other hand we would like some functions, in particular these low level
# wrapperst to accept only ASTS (and not numbers).

# Also for asts which represent variables we have a sort/type that we want
# represented in the type of the variable.

# Lastly there are expressions of different type that we would like to be
# subtypes of different types of real, e.g an Integer is not a type of Floating.

# Solution
# - CCall AST files return (UnknownAst / Ast)
# - VarAst{T <: MathNumber}, e.g. Var{Real} is not right because you can make a variable of any sort, including tuple and array nad mayve defined ine there
# VarAst{T <: Sort} <: .. Then we can't write functions

# NumericalVarAst{T <: MathNumber} <: Real -- What about Integer

## AST Solution
# 1. Make them all subset of the Real
# 2. Make them subset of individual type and use unions to group them

typealias MathNumber Union{Real, Integer, Bool}

type Ast <: Z3CType ptr::AstPtr end

"numeral constants"
type NumeralAst{T <: MathNumber} <: Real
  ptr::Z3_ast
end

"(fuction?) application"
type AppAst{T} <: Real
  ptr::Z3_ast
end

"(fuction?) application resulting in real valued variable"
type RealAppAst{T <: MathNumber} <: Real
  ptr::Z3_ast
end

"bound variables of type `T`"
type VarAst{T}
  ptr::Z3_ast
end

"Real Valued Variable of numeric type `T`"
type RealVarAst{T <: MathNumber} <: Real
  ptr::Z3_ast
  i::Integer #FIXME: Should this be here?
end

"quantifiers"
type QuantifierAst
  ptr::Z3_ast
end

"sort"
type SortAst
  ptr::Z3_ast
end

"function declaration"
type FuncDeclAst
  ptr::Z3_ast
end

"internal"
type UnknownAst
  ptr::Z3_ast
end

AbstractAst = Union{Ast, AppAst, VarAst, RealVarAst, QuantifierAst, SortAst, FuncDeclAst, NumeralAst, UnknownAst}
convert(::Type{AbstractAst}, x::Ptr{Void}) = Ast(x)
convert{T <: AbstractAst}(::Type{Ptr{Void}}, x::T) = x.ptr
convert{T <: AbstractAst}(::Type{T}, x::AbstractAst) = T(x.ptr)

type App <: Z3CType ptr::AppPtr end
type Pattern <: Z3CType ptr::PatternPtr end
type Model <: Z3CType ptr::ModelPtr end
type Constructor <: Z3CType ptr::ConstructorPtr end
type ConstructorList <: Z3CType ptr::ConstructorListPtr end
type Params <: Z3CType ptr::ParamsPtr end
type ParamDescrs <: Z3CType ptr::ParamDescrsPtr end
type Goal <: Z3CType ptr::GoalPtr end
type Tactic <: Z3CType ptr::TacticPtr end
type Probe <: Z3CType ptr::ProbePtr end
type Stats <: Z3CType ptr::StatsPtr end
type Solver <: Z3CType ptr::SolverPtr end
type AstVector <: Z3CType ptr::AstVectorPtr end
type AstMap <: Z3CType ptr::AstMapPtr end
type ApplyResult <: Z3CType ptr::ApplyResultPtr end
type FuncInterp <: Z3CType ptr::FuncInterpPtr end
type FuncEntry <: Z3CType ptr::FuncEntryPtr end
type Fixedpoint <: Z3CType ptr::FixedpointPtr end
type RcfNum <: Z3CType ptr::RcfNumPtr end
type TheoryData <: Z3CType ptr::TheoryDataPtr end #Is actually a void ptr

## Function Typedefs
type ReduceEqCallbackFptr <: Z3CType ptr::ReduceEqCallbackFptrPtr end
type ReduceAppCallbackFptr <: Z3CType ptr::ReduceAppCallbackFptrPtr end
type ReduceDistinctCallbackFptr <: Z3CType ptr::ReduceDistinctCallbackFptrPtr end
type TheoryCallbackFptr <: Z3CType ptr::TheoryCallbackFptrPtr end
type TheoryFinalCheckCallbackFptr <: Z3CType ptr::TheoryFinalCheckCallbackFptrPtr end
type TheoryAstBoolCallbackFptr <: Z3CType ptr::TheoryAstBoolCallbackFptrPtr end
type TheoryAstAstCallbackFptr <: Z3CType ptr::TheoryAstAstCallbackFptrPtr end
type TheoryAstCallbackFptr <: Z3CType ptr::TheoryAstCallbackFptrPtr end

type FixedpointReduceAssignCallbackFptr <: Z3CType ptr::FixedpointReduceAssignCallbackFptrPtr end
type FixedpointReduceAppCallbackFptr <: Z3CType ptr::FixedpointReduceAppCallbackFptrPtr end

## arg/return type Conversion
## ==========================

convert(::Type{Ptr{Void}}, x::Z3CType) = x.ptr
convert(::Type{Z3_string}, x::ASCIIString) = pointer(x)


#FIME: Vector is too loose of a type, should be Vector{T<:AbstractAst}
convert(::Type{Ptr{Z3_ast}}, x::Vector) = pointer(Ptr{Void}[a.ptr for a in x])
convert{T<:Z3CType}(::Type{T}, x::Ptr{Void}) = T(x)
convert(::Type{ASCIIString}, x::Z3_string) = bytestring(x)

## Enums
## =====
# "Lifted Boolean type: \c false, \c undefined, \c true."
@enum Z3_lbool Z3_L_FALSE = -1 Z3_L_UNDEF Z3_L_TRUE

# """The different kinds of symbol.
# In Z3, a symbol can be represented using integers and strings"""
@enum Z3_symbol_kind Z3_INT_SYMBOL Z3_STRING_SYMBOL

@enum Z3_parameter_kind Z3_PARAMETER_INT Z3_PARAMETER_DOUBLE Z3_PARAMETER_RATIONAL Z3_PARAMETER_SYMBOL Z3_PARAMETER_SORT Z3_PARAMETER_AST Z3_PARAMETER_FUNC_DECL

# "The different kinds of Z3 types"
@enum Z3_sort_kind Z3_UNINTERPRETED_SORT Z3_BOOL_SORT Z3_INT_SORT Z3_REAL_SORT Z3_BV_SORT Z3_ARRAY_SORT Z3_DATATYPE_SORT Z3_RELATION_SORT Z3_FINITE_DOMAIN_SORT Z3_UNKNOWN_SORT = 1000

# "The different kinds of Z3 AST (abstract syntax trees). That is, terms, formulas and types."
@enum Z3_ast_kind Z3_NUMERAL_AST Z3_APP_AST Z3_VAR_AST Z3_QUANTIFIER_AST Z3_SORT_AST Z3_FUNC_DECL_AST Z3_UNKNOWN_AST = 1000

# "The different kinds of interpreted function kinds."
@enum(Z3_decl_kind,
    # Basic
    Z3_OP_TRUE = 0x100,
    Z3_OP_FALSE,
    Z3_OP_EQ,
    Z3_OP_DISTINCT,
    Z3_OP_ITE,
    Z3_OP_AND,
    Z3_OP_OR,
    Z3_OP_IFF,
    Z3_OP_XOR,
    Z3_OP_NOT,
    Z3_OP_IMPLIES,
    Z3_OP_OEQ,
    Z3_OP_INTERP,

    # Arithmetic
    Z3_OP_ANUM = 0x200,
    Z3_OP_AGNUM,
    Z3_OP_LE,
    Z3_OP_GE,
    Z3_OP_LT,
    Z3_OP_GT,
    Z3_OP_ADD,
    Z3_OP_SUB,
    Z3_OP_UMINUS,
    Z3_OP_MUL,
    Z3_OP_DIV,
    Z3_OP_IDIV,
    Z3_OP_REM,
    Z3_OP_MOD,
    Z3_OP_TO_REAL,
    Z3_OP_TO_INT,
    Z3_OP_IS_INT,
    Z3_OP_POWER,

    # Arrays & Sets
    Z3_OP_STORE = 0x300,
    Z3_OP_SELECT,
    Z3_OP_CONST_ARRAY,
    Z3_OP_ARRAY_MAP,
    Z3_OP_ARRAY_DEFAULT,
    Z3_OP_SET_UNION,
    Z3_OP_SET_INTERSECT,
    Z3_OP_SET_DIFFERENCE,
    Z3_OP_SET_COMPLEMENT,
    Z3_OP_SET_SUBSET,
    Z3_OP_AS_ARRAY,

    # Bit-vectors
    Z3_OP_BNUM = 0x400,
    Z3_OP_BIT1,
    Z3_OP_BIT0,
    Z3_OP_BNEG,
    Z3_OP_BADD,
    Z3_OP_BSUB,
    Z3_OP_BMUL,

    Z3_OP_BSDIV,
    Z3_OP_BUDIV,
    Z3_OP_BSREM,
    Z3_OP_BUREM,
    Z3_OP_BSMOD,

    # special functions to record the division by 0 cases
    # these are internal functions
    Z3_OP_BSDIV0,
    Z3_OP_BUDIV0,
    Z3_OP_BSREM0,
    Z3_OP_BUREM0,
    Z3_OP_BSMOD0,

    Z3_OP_ULEQ,
    Z3_OP_SLEQ,
    Z3_OP_UGEQ,
    Z3_OP_SGEQ,
    Z3_OP_ULT,
    Z3_OP_SLT,
    Z3_OP_UGT,
    Z3_OP_SGT,

    Z3_OP_BAND,
    Z3_OP_BOR,
    Z3_OP_BNOT,
    Z3_OP_BXOR,
    Z3_OP_BNAND,
    Z3_OP_BNOR,
    Z3_OP_BXNOR,

    Z3_OP_CONCAT,
    Z3_OP_SIGN_EXT,
    Z3_OP_ZERO_EXT,
    Z3_OP_EXTRACT,
    Z3_OP_REPEAT,

    Z3_OP_BREDOR,
    Z3_OP_BREDAND,
    Z3_OP_BCOMP,

    Z3_OP_BSHL,
    Z3_OP_BLSHR,
    Z3_OP_BASHR,
    Z3_OP_ROTATE_LEFT,
    Z3_OP_ROTATE_RIGHT,
    Z3_OP_EXT_ROTATE_LEFT,
    Z3_OP_EXT_ROTATE_RIGHT,

    Z3_OP_INT2BV,
    Z3_OP_BV2INT,
    Z3_OP_CARRY,
    Z3_OP_XOR3,

    # Proofs
    Z3_OP_PR_UNDEF = 0x500,
    Z3_OP_PR_TRUE,
    Z3_OP_PR_ASSERTED,
    Z3_OP_PR_GOAL,
    Z3_OP_PR_MODUS_PONENS,
    Z3_OP_PR_REFLEXIVITY,
    Z3_OP_PR_SYMMETRY,
    Z3_OP_PR_TRANSITIVITY,
    Z3_OP_PR_TRANSITIVITY_STAR,
    Z3_OP_PR_MONOTONICITY,
    Z3_OP_PR_QUANT_INTRO,
    Z3_OP_PR_DISTRIBUTIVITY,
    Z3_OP_PR_AND_ELIM,
    Z3_OP_PR_NOT_OR_ELIM,
    Z3_OP_PR_REWRITE,
    Z3_OP_PR_REWRITE_STAR,
    Z3_OP_PR_PULL_QUANT,
    Z3_OP_PR_PULL_QUANT_STAR,
    Z3_OP_PR_PUSH_QUANT,
    Z3_OP_PR_ELIM_UNUSED_VARS,
    Z3_OP_PR_DER,
    Z3_OP_PR_QUANT_INST,
    Z3_OP_PR_HYPOTHESIS,
    Z3_OP_PR_LEMMA,
    Z3_OP_PR_UNIT_RESOLUTION,
    Z3_OP_PR_IFF_TRUE,
    Z3_OP_PR_IFF_FALSE,
    Z3_OP_PR_COMMUTATIVITY,
    Z3_OP_PR_DEF_AXIOM,
    Z3_OP_PR_DEF_INTRO,
    Z3_OP_PR_APPLY_DEF,
    Z3_OP_PR_IFF_OEQ,
    Z3_OP_PR_NNF_POS,
    Z3_OP_PR_NNF_NEG,
    Z3_OP_PR_NNF_STAR,
    Z3_OP_PR_CNF_STAR,
    Z3_OP_PR_SKOLEMIZE,
    Z3_OP_PR_MODUS_PONENS_OEQ,
    Z3_OP_PR_TH_LEMMA,
    Z3_OP_PR_HYPER_RESOLVE,

    # Sequences
    Z3_OP_RA_STORE = 0x600,
    Z3_OP_RA_EMPTY,
    Z3_OP_RA_IS_EMPTY,
    Z3_OP_RA_JOIN,
    Z3_OP_RA_UNION,
    Z3_OP_RA_WIDEN,
    Z3_OP_RA_PROJECT,
    Z3_OP_RA_FILTER,
    Z3_OP_RA_NEGATION_FILTER,
    Z3_OP_RA_RENAME,
    Z3_OP_RA_COMPLEMENT,
    Z3_OP_RA_SELECT,
    Z3_OP_RA_CLONE,
    Z3_OP_FD_LT,

    # Auxiliary
    Z3_OP_LABEL = 0x700,
    Z3_OP_LABEL_LIT,

    # Datatypes
    Z3_OP_DT_CONSTRUCTOR=0x800,
    Z3_OP_DT_RECOGNISER,
    Z3_OP_DT_ACCESSOR,

    Z3_OP_UNINTERPRETED)

# "The different kinds of parameters that can be associated with parameter sets."
@enum(Z3_param_kind,
      Z3_PK_UINT,
      Z3_PK_BOOL,
      Z3_PK_DOUBLE,
      Z3_PK_SYMBOL,
      Z3_PK_STRING,
      Z3_PK_OTHER,
      Z3_PK_INVALID)

# "The different kinds of search failure types."
@enum(Z3_search_failure,
      Z3_NO_FAILURE,
      Z3_UNKNOWN,
      Z3_TIMEOUT,
      Z3_MEMOUT_WATERMARK,
      Z3_CANCELED,
      Z3_NUM_CONFLICTS,
      Z3_THEORY,
      Z3_QUANTIFIERS)

# "Z3 pretty printing modes (See #Z3_set_ast_print_mode)."
@enum(Z3_ast_print_mode,
      Z3_PRINT_SMTLIB_FULL,
      Z3_PRINT_LOW_LEVEL,
      Z3_PRINT_SMTLIB_COMPLIANT,
      Z3_PRINT_SMTLIB2_COMPLIANT)

@enum(Z3_ast_print_mode,
    Z3_PRINT_SMTLIB_FULL,
    Z3_PRINT_LOW_LEVEL,
    Z3_PRINT_SMTLIB_COMPLIANT,
    Z3_PRINT_SMTLIB2_COMPLIANT)

@enum(Z3_error_code,
      Z3_OK,
      Z3_SORT_ERROR,
      Z3_IOB,
      Z3_INVALID_ARG,
      Z3_PARSER_ERROR,
      Z3_NO_PARSER,
      Z3_INVALID_PATTERN,
      Z3_MEMOUT_FAIL,
      Z3_FILE_ACCESS_ERROR,
      Z3_INTERNAL_FATAL,
      Z3_INVALID_USAGE,
      Z3_DEC_REF_ERROR,
      Z3_EXCEPTION)

@enum(Z3_goal_prec,
  Z3_GOAL_PRECISE,
  Z3_GOAL_UNDER,
  Z3_GOAL_OVER,
  Z3_GOAL_UNDER_OVER)

## Enum Conversion
#FIXME, make this more general
# convert(::)

## Macros
## ======
z3tojulia = Dict{Symbol, Symbol}(:Z3_symbol => :Z3Symbol,
            :Z3_literals => :Literals,
            :Z3_theory => :Theory,
            :Z3_config => :Config,
            :Z3_context => :Context,
            :Z3_sort => :Sort, #Assume we don't known what sort it is
            :Z3_func_decl => :FuncDecl,
            :Z3_ast => :AbstractAst, # Many kinds of Ast
            :Z3_app => :App,
            :Z3_pattern => :Pattern,
            :Z3_model => :Model,
            :Z3_constructor => :Constructor,
            :Z3_constructor_list => :ConstructorList,
            :Z3_params => :Params,
            :Z3_param_descrs => :ParamDescrs,
            :Z3_goal => :Goal,
            :Z3_tactic => :Tactic,
            :Z3_probe => :Probe,
            :Z3_stats => :Stats,
            :Z3_solver => :Solver,
            :Z3_ast_vector => :AstVector,
            :Z3_ast_map => :AstMap,
            :Z3_apply_result => :ApplyResult,
            :Z3_func_interp => :FuncInterp,
            :Z3_func_entry => :FuncEntry,
            :Z3_fixedpoint => :Fixedpoint,
            :Z3_rcf_num => :RcfNum,
            :Z3_theory_data => :TheoryData,
            :Z3_reduce_eq_callback_fptr => :ReduceEqCallbackFptr,
            :Z3_reduce_app_callback_fptr => :ReduceAppCallbackFptr,
            :Z3_reduce_distinct_callback_fptr => :ReduceDistinctCallbackFptr,
            :Z3_theory_callback_fptr => :TheoryCallbackFptr,
            :Z3_theory_final_check_callback_fptr => :TheoryFinalCheckCallbackFptr,
            :Z3_theory_ast_bool_callback_fptr => :TheoryAstBoolCallbackFptr,
            :Z3_theory_ast_ast_callback_fptr => :TheoryAstAstCallbackFptr,
            :Z3_theory_ast_callback_fptr => :TheoryAstCallbackFptr,
            :Z3_bool => :Z3Bool,
            :Z3_error_handler => :FixedpointReduceAssignCallbackFptr,
            :Z3_fixedpoint_reduce_assign_callback_fptr => :FixedpointReduceAssignCallbackFptr,
            :Z3_fixedpoint_reduce_app_callback_fptr => :FixedpointReduceAppCallbackFptr)

arg_name(arg::Expr) = arg.args[1]::Symbol
arg_type(arg::Expr) = arg.args[2]

"Maps Z3 typealias symbols to corresponding Julia types"
function convert_typ(typ::Union{Symbol, Expr})
  if typ == :(Z3_string)
    :ASCIIString
  elseif typ == :(Ptr{Z3_ast})
    :(Vector)
  elseif haskey(z3tojulia, typ)
    z3tojulia[typ]
  else
    typ
  end
end

"Maps Z3 typealias symbols to corresponding Julia types"
function convert_arg(arg::Expr)
  typ = arg_type(arg)
  name = arg_name(arg)
  new_typ = convert_typ(typ)
  Expr(:(::), arg_name(arg), new_typ)
end

function handle_call(arg::Expr)
  typ = arg_type(arg)
  name = arg_name(arg)
  :(convert($typ, $name))
end

"""For a z3 ccall wrapper function (below), `wrap` creates an additional function
which accepts the Julia wrapper types and does necessary conversions"""
macro wrap(func_def)
  # FIXME: finding return_type in this way is very brittle
  return_type = func_def.args[2].args[2].args[2]
  name = func_def.args[1].args[1]
  @compat short_name = Symbol(string(name)[4:end])
  func_args = func_def.args[1].args[2:end]

  new_return_typ = convert_typ(return_type)

  converted_args = [convert_arg(arg) for arg in func_args]
  params = Expr(:call, short_name, converted_args...)
  api_call = Expr(:call, name, [handle_call(arg) for arg in func_args]...)
  wrapped_call = Expr(:call, :convert, new_return_typ, api_call)
  func_decl = Expr(:function, params, wrapped_call)

  # If first arg is ctx, make a kwarg version of the function
  if length(func_args) > 0 && arg_type(func_args[1]) == :(Z3_context)
    kw_params = Expr(:parameters, Expr(:kw, Expr(:(::), :ctx, :Context), Expr(:call, :global_ctx)))
    kw_params2 = Expr(:call, short_name, kw_params, converted_args[2:end]...)
    kw_decl = Expr(:function, kw_params2, wrapped_call)
    esc(func_def)
    :(begin
       $(esc(func_def))
       $(esc(func_decl))
       $(esc(kw_decl))
       export $short_name
      end)
  else
    esc(func_def)
    :(begin
       $(esc(func_def))
       $(esc(func_decl))
       export $short_name
      end)
  end
end

## functions
## =========

function Z3_global_param_set(param_id::Z3_string,param_value::Z3_string)
    ccall((:Z3_global_param_set,"libz3"),Void,(Z3_string,Z3_string),param_id,param_value)
end

@wrap function Z3_global_param_reset_all()
    ccall((:Z3_global_param_reset_all,"libz3"),Void,())
end

@wrap function Z3_global_param_get(param_id::Z3_string,param_value::Z3_string_ptr)
    ccall((:Z3_global_param_get,"libz3"),Z3_bool,(Z3_string,Z3_string_ptr),param_id,param_value)
end

@wrap function Z3_mk_config()
    ccall((:Z3_mk_config,"libz3"),Z3_config,())
end

@wrap function Z3_del_config(c::Z3_config)
    ccall((:Z3_del_config,"libz3"),Void,(Z3_config,),c)
end

@wrap function Z3_set_param_value(c::Z3_config,param_id::Z3_string,param_value::Z3_string)
    ccall((:Z3_set_param_value,"libz3"),Void,(Z3_config,Z3_string,Z3_string),c,param_id,param_value)
end

@wrap function Z3_mk_context(c::Z3_config)
    ccall((:Z3_mk_context,"libz3"),Z3_context,(Z3_config,),c)
end

@wrap function Z3_mk_context_rc(c::Z3_config)
    ccall((:Z3_mk_context_rc,"libz3"),Z3_context,(Z3_config,),c)
end

@wrap function Z3_del_context(ctx::Z3_context)
    ccall((:Z3_del_context,"libz3"),Void,(Z3_context,),ctx)
end

@wrap function Z3_inc_ref(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_inc_ref,"libz3"),Void,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_dec_ref(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_dec_ref,"libz3"),Void,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_update_param_value(ctx::Z3_context,param_id::Z3_string,param_value::Z3_string)
    ccall((:Z3_update_param_value,"libz3"),Void,(Z3_context,Z3_string,Z3_string),ctx,param_id,param_value)
end

@wrap function Z3_interrupt(ctx::Z3_context)
    ccall((:Z3_interrupt,"libz3"),Void,(Z3_context,),ctx)
end

@wrap function Z3_mk_params(ctx::Z3_context)
    ccall((:Z3_mk_params,"libz3"),Z3_params,(Z3_context,),ctx)
end

@wrap function Z3_params_inc_ref(ctx::Z3_context,p::Z3_params)
    ccall((:Z3_params_inc_ref,"libz3"),Void,(Z3_context,Z3_params),ctx,p)
end

@wrap function Z3_params_dec_ref(ctx::Z3_context,p::Z3_params)
    ccall((:Z3_params_dec_ref,"libz3"),Void,(Z3_context,Z3_params),ctx,p)
end

@wrap function Z3_params_set_bool(ctx::Z3_context,p::Z3_params,k::Z3_symbol,v::Z3_bool)
    ccall((:Z3_params_set_bool,"libz3"),Void,(Z3_context,Z3_params,Z3_symbol,Z3_bool),ctx,p,k,v)
end

@wrap function Z3_params_set_uint(ctx::Z3_context,p::Z3_params,k::Z3_symbol,v::UInt32)
    ccall((:Z3_params_set_uint,"libz3"),Void,(Z3_context,Z3_params,Z3_symbol,UInt32),ctx,p,k,v)
end

@wrap function Z3_params_set_double(ctx::Z3_context,p::Z3_params,k::Z3_symbol,v::Cdouble)
    ccall((:Z3_params_set_double,"libz3"),Void,(Z3_context,Z3_params,Z3_symbol,Cdouble),ctx,p,k,v)
end

@wrap function Z3_params_set_symbol(ctx::Z3_context,p::Z3_params,k::Z3_symbol,v::Z3_symbol)
    ccall((:Z3_params_set_symbol,"libz3"),Void,(Z3_context,Z3_params,Z3_symbol,Z3_symbol),ctx,p,k,v)
end

@wrap function Z3_params_to_string(ctx::Z3_context,p::Z3_params)
    ccall((:Z3_params_to_string,"libz3"),Z3_string,(Z3_context,Z3_params),ctx,p)
end

@wrap function Z3_params_validate(ctx::Z3_context,p::Z3_params,d::Z3_param_descrs)
    ccall((:Z3_params_validate,"libz3"),Void,(Z3_context,Z3_params,Z3_param_descrs),ctx,p,d)
end

@wrap function Z3_param_descrs_inc_ref(ctx::Z3_context,p::Z3_param_descrs)
    ccall((:Z3_param_descrs_inc_ref,"libz3"),Void,(Z3_context,Z3_param_descrs),ctx,p)
end

@wrap function Z3_param_descrs_dec_ref(ctx::Z3_context,p::Z3_param_descrs)
    ccall((:Z3_param_descrs_dec_ref,"libz3"),Void,(Z3_context,Z3_param_descrs),ctx,p)
end

@wrap function Z3_param_descrs_get_kind(ctx::Z3_context,p::Z3_param_descrs,n::Z3_symbol)
    ccall((:Z3_param_descrs_get_kind,"libz3"),Z3_param_kind,(Z3_context,Z3_param_descrs,Z3_symbol),ctx,p,n)
end

@wrap function Z3_param_descrs_size(ctx::Z3_context,p::Z3_param_descrs)
    ccall((:Z3_param_descrs_size,"libz3"),UInt32,(Z3_context,Z3_param_descrs),ctx,p)
end

@wrap function Z3_param_descrs_get_name(ctx::Z3_context,p::Z3_param_descrs,i::UInt32)
    ccall((:Z3_param_descrs_get_name,"libz3"),Z3_symbol,(Z3_context,Z3_param_descrs,UInt32),ctx,p,i)
end

@wrap function Z3_param_descrs_to_string(ctx::Z3_context,p::Z3_param_descrs)
    ccall((:Z3_param_descrs_to_string,"libz3"),Z3_string,(Z3_context,Z3_param_descrs),ctx,p)
end

@wrap function Z3_mk_int_symbol(ctx::Z3_context,i::Cint)
    ccall((:Z3_mk_int_symbol,"libz3"),Z3_symbol,(Z3_context,Cint),ctx,i)
end

@wrap function Z3_mk_string_symbol(ctx::Z3_context,s::Z3_string)
    ccall((:Z3_mk_string_symbol,"libz3"),Z3_symbol,(Z3_context,Z3_string),ctx,s)
end

@wrap function Z3_mk_uninterpreted_sort(ctx::Z3_context,s::Z3_symbol)
    ccall((:Z3_mk_uninterpreted_sort,"libz3"),Z3_sort,(Z3_context,Z3_symbol),ctx,s)
end

@wrap function Z3_mk_bool_sort(ctx::Z3_context)
    ccall((:Z3_mk_bool_sort,"libz3"),Z3_sort,(Z3_context,),ctx)
end

@wrap function Z3_mk_int_sort(ctx::Z3_context)
    ccall((:Z3_mk_int_sort,"libz3"),Z3_sort,(Z3_context,),ctx)
end

@wrap function Z3_mk_real_sort(ctx::Z3_context)
    ccall((:Z3_mk_real_sort,"libz3"),Z3_sort,(Z3_context,),ctx)
end

@wrap function Z3_mk_bv_sort(ctx::Z3_context,sz::UInt32)
    ccall((:Z3_mk_bv_sort,"libz3"),Z3_sort,(Z3_context,UInt32),ctx,sz)
end

@wrap function Z3_mk_finite_domain_sort(ctx::Z3_context,name::Z3_symbol,size::Culonglong)
    ccall((:Z3_mk_finite_domain_sort,"libz3"),Z3_sort,(Z3_context,Z3_symbol,Culonglong),ctx,name,size)
end

@wrap function Z3_mk_array_sort(ctx::Z3_context,domain::Z3_sort,range::Z3_sort)
    ccall((:Z3_mk_array_sort,"libz3"),Z3_sort,(Z3_context,Z3_sort,Z3_sort),ctx,domain,range)
end

@wrap function Z3_mk_tuple_sort(ctx::Z3_context,mk_tuple_name::Z3_symbol,num_fields::UInt32,field_names::Ptr{Z3_symbol},field_sorts::Ptr{Z3_sort},mk_tuple_decl::Ptr{Z3_func_decl},proj_decl::Ptr{Z3_func_decl})
    ccall((:Z3_mk_tuple_sort,"libz3"),Z3_sort,(Z3_context,Z3_symbol,UInt32,Ptr{Z3_symbol},Ptr{Z3_sort},Ptr{Z3_func_decl},Ptr{Z3_func_decl}),ctx,mk_tuple_name,num_fields,field_names,field_sorts,mk_tuple_decl,proj_decl)
end

@wrap function Z3_mk_enumeration_sort(ctx::Z3_context,name::Z3_symbol,n::UInt32,enum_names::Ptr{Z3_symbol},enum_consts::Ptr{Z3_func_decl},enum_testers::Ptr{Z3_func_decl})
    ccall((:Z3_mk_enumeration_sort,"libz3"),Z3_sort,(Z3_context,Z3_symbol,UInt32,Ptr{Z3_symbol},Ptr{Z3_func_decl},Ptr{Z3_func_decl}),ctx,name,n,enum_names,enum_consts,enum_testers)
end

@wrap function Z3_mk_list_sort(ctx::Z3_context,name::Z3_symbol,elem_sort::Z3_sort,nil_decl::Ptr{Z3_func_decl},is_nil_decl::Ptr{Z3_func_decl},ctxons_decl::Ptr{Z3_func_decl},is_cons_decl::Ptr{Z3_func_decl},head_decl::Ptr{Z3_func_decl},tail_decl::Ptr{Z3_func_decl})
    ccall((:Z3_mk_list_sort,"libz3"),Z3_sort,(Z3_context,Z3_symbol,Z3_sort,Ptr{Z3_func_decl},Ptr{Z3_func_decl},Ptr{Z3_func_decl},Ptr{Z3_func_decl},Ptr{Z3_func_decl},Ptr{Z3_func_decl}),ctx,name,elem_sort,nil_decl,is_nil_decl,ctxons_decl,is_cons_decl,head_decl,tail_decl)
end

@wrap function Z3_mk_constructor(ctx::Z3_context,name::Z3_symbol,recognizer::Z3_symbol,num_fields::UInt32,field_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},sort_refs::Ref{UInt32})
    ccall((:Z3_mk_constructor,"libz3"),Z3_constructor,(Z3_context,Z3_symbol,Z3_symbol,UInt32,Ptr{Z3_symbol},Ptr{Z3_sort},Ref{UInt32}),ctx,name,recognizer,num_fields,field_names,sorts,sort_refs)
end

@wrap function Z3_del_constructor(ctx::Z3_context,ctxonstr::Z3_constructor)
    ccall((:Z3_del_constructor,"libz3"),Void,(Z3_context,Z3_constructor),ctx,ctxonstr)
end

@wrap function Z3_mk_datatype(ctx::Z3_context,name::Z3_symbol,num_constructors::UInt32,ctxonstructors::Ptr{Z3_constructor})
    ccall((:Z3_mk_datatype,"libz3"),Z3_sort,(Z3_context,Z3_symbol,UInt32,Ptr{Z3_constructor}),ctx,name,num_constructors,ctxonstructors)
end

@wrap function Z3_mk_constructor_list(ctx::Z3_context,num_constructors::UInt32,ctxonstructors::Ptr{Z3_constructor})
    ccall((:Z3_mk_constructor_list,"libz3"),Z3_constructor_list,(Z3_context,UInt32,Ptr{Z3_constructor}),ctx,num_constructors,ctxonstructors)
end

@wrap function Z3_del_constructor_list(ctx::Z3_context,ctxlist::Z3_constructor_list)
    ccall((:Z3_del_constructor_list,"libz3"),Void,(Z3_context,Z3_constructor_list),ctx,ctxlist)
end

@wrap function Z3_mk_datatypes(ctx::Z3_context,num_sorts::UInt32,sort_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},ctxonstructor_lists::Ptr{Z3_constructor_list})
    ccall((:Z3_mk_datatypes,"libz3"),Void,(Z3_context,UInt32,Ptr{Z3_symbol},Ptr{Z3_sort},Ptr{Z3_constructor_list}),ctx,num_sorts,sort_names,sorts,ctxonstructor_lists)
end

@wrap function Z3_query_constructor(ctx::Z3_context,ctxonstr::Z3_constructor,num_fields::UInt32,ctxonstructor::Ptr{Z3_func_decl},tester::Ptr{Z3_func_decl},accessors::Ptr{Z3_func_decl})
    ccall((:Z3_query_constructor,"libz3"),Void,(Z3_context,Z3_constructor,UInt32,Ptr{Z3_func_decl},Ptr{Z3_func_decl},Ptr{Z3_func_decl}),ctx,ctxonstr,num_fields,ctxonstructor,tester,accessors)
end

@wrap function Z3_mk_func_decl(ctx::Z3_context,s::Z3_symbol,domain_size::UInt32,domain::Ptr{Z3_sort},range::Z3_sort)
    ccall((:Z3_mk_func_decl,"libz3"),Z3_func_decl,(Z3_context,Z3_symbol,UInt32,Ptr{Z3_sort},Z3_sort),ctx,s,domain_size,domain,range)
end

@wrap function Z3_mk_app(ctx::Z3_context,d::Z3_func_decl,num_args::UInt32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_app,"libz3"),Z3_ast,(Z3_context,Z3_func_decl,UInt32,Ptr{Z3_ast}),ctx,d,num_args,args)
end

@wrap function Z3_mk_const(ctx::Z3_context,s::Z3_symbol,ty::Z3_sort)
    ccall((:Z3_mk_const,"libz3"),Z3_ast,(Z3_context,Z3_symbol,Z3_sort),ctx,s,ty)
end

@wrap function Z3_mk_fresh_func_decl(ctx::Z3_context,prefix::Z3_string,domain_size::UInt32,domain::Ptr{Z3_sort},range::Z3_sort)
    ccall((:Z3_mk_fresh_func_decl,"libz3"),Z3_func_decl,(Z3_context,Z3_string,UInt32,Ptr{Z3_sort},Z3_sort),ctx,prefix,domain_size,domain,range)
end

@wrap function Z3_mk_fresh_const(ctx::Z3_context,prefix::Z3_string,ty::Z3_sort)
    ccall((:Z3_mk_fresh_const,"libz3"),Z3_ast,(Z3_context,Z3_string,Z3_sort),ctx,prefix,ty)
end

@wrap function Z3_mk_true(ctx::Z3_context)
    ccall((:Z3_mk_true,"libz3"),Z3_ast,(Z3_context,),ctx)
end

@wrap function Z3_mk_false(ctx::Z3_context)
    ccall((:Z3_mk_false,"libz3"),Z3_ast,(Z3_context,),ctx)
end

@wrap function Z3_mk_eq(ctx::Z3_context,l::Z3_ast,r::Z3_ast)
    ccall((:Z3_mk_eq,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,l,r)
end

@wrap function Z3_mk_distinct(ctx::Z3_context,num_args::UInt32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_distinct,"libz3"),Z3_ast,(Z3_context,UInt32,Ptr{Z3_ast}),ctx,num_args,args)
end

@wrap function Z3_mk_not(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_mk_not,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_mk_ite(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast,t3::Z3_ast)
    ccall((:Z3_mk_ite,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast,Z3_ast),ctx,t1,t2,t3)
end

@wrap function Z3_mk_iff(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_iff,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_implies(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_implies,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_xor(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_xor,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_and(ctx::Z3_context,num_args::UInt32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_and,"libz3"),Z3_ast,(Z3_context,UInt32,Ptr{Z3_ast}),ctx,num_args,args)
end

@wrap function Z3_mk_or(ctx::Z3_context,num_args::UInt32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_or,"libz3"),Z3_ast,(Z3_context,UInt32,Ptr{Z3_ast}),ctx,num_args,args)
end

@wrap function Z3_mk_add(ctx::Z3_context,num_args::UInt32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_add,"libz3"),Z3_ast,(Z3_context,UInt32,Ptr{Z3_ast}),ctx,num_args,args)
end

@wrap function Z3_mk_mul(ctx::Z3_context,num_args::UInt32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_mul,"libz3"),Z3_ast,(Z3_context,UInt32,Ptr{Z3_ast}),ctx,num_args,args)
end

@wrap function Z3_mk_sub(ctx::Z3_context,num_args::UInt32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_sub,"libz3"),Z3_ast,(Z3_context,UInt32,Ptr{Z3_ast}),ctx,num_args,args)
end

@wrap function Z3_mk_unary_minus(ctx::Z3_context,arg::Z3_ast)
    ccall((:Z3_mk_unary_minus,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,arg)
end

@wrap function Z3_mk_div(ctx::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_div,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,arg1,arg2)
end

@wrap function Z3_mk_mod(ctx::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_mod,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,arg1,arg2)
end

@wrap function Z3_mk_rem(ctx::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_rem,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,arg1,arg2)
end

@wrap function Z3_mk_power(ctx::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_power,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,arg1,arg2)
end

@wrap function Z3_mk_lt(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_lt,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_le(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_le,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_gt(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_gt,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_ge(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_ge,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_int2real(ctx::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_int2real,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,t1)
end

@wrap function Z3_mk_real2int(ctx::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_real2int,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,t1)
end

@wrap function Z3_mk_is_int(ctx::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_is_int,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,t1)
end

@wrap function Z3_mk_bvnot(ctx::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_bvnot,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,t1)
end

@wrap function Z3_mk_bvredand(ctx::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_bvredand,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,t1)
end

@wrap function Z3_mk_bvredor(ctx::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_bvredor,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,t1)
end

@wrap function Z3_mk_bvand(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvand,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvor(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvor,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvxor(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvxor,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvnand(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvnand,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvnor(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvnor,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvxnor(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvxnor,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvneg(ctx::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_bvneg,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,t1)
end

@wrap function Z3_mk_bvadd(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvadd,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvsub(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsub,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvmul(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvmul,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvudiv(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvudiv,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvsdiv(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsdiv,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvurem(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvurem,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvsrem(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsrem,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvsmod(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsmod,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvult(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvult,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvslt(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvslt,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvule(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvule,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvsle(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsle,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvuge(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvuge,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvsge(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsge,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvugt(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvugt,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvsgt(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsgt,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_concat(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_concat,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_extract(ctx::Z3_context,high::UInt32,low::UInt32,t1::Z3_ast)
    ccall((:Z3_mk_extract,"libz3"),Z3_ast,(Z3_context,UInt32,UInt32,Z3_ast),ctx,high,low,t1)
end

@wrap function Z3_mk_sign_ext(ctx::Z3_context,i::UInt32,t1::Z3_ast)
    ccall((:Z3_mk_sign_ext,"libz3"),Z3_ast,(Z3_context,UInt32,Z3_ast),ctx,i,t1)
end

@wrap function Z3_mk_zero_ext(ctx::Z3_context,i::UInt32,t1::Z3_ast)
    ccall((:Z3_mk_zero_ext,"libz3"),Z3_ast,(Z3_context,UInt32,Z3_ast),ctx,i,t1)
end

@wrap function Z3_mk_repeat(ctx::Z3_context,i::UInt32,t1::Z3_ast)
    ccall((:Z3_mk_repeat,"libz3"),Z3_ast,(Z3_context,UInt32,Z3_ast),ctx,i,t1)
end

@wrap function Z3_mk_bvshl(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvshl,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvlshr(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvlshr,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvashr(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvashr,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_rotate_left(ctx::Z3_context,i::UInt32,t1::Z3_ast)
    ccall((:Z3_mk_rotate_left,"libz3"),Z3_ast,(Z3_context,UInt32,Z3_ast),ctx,i,t1)
end

@wrap function Z3_mk_rotate_right(ctx::Z3_context,i::UInt32,t1::Z3_ast)
    ccall((:Z3_mk_rotate_right,"libz3"),Z3_ast,(Z3_context,UInt32,Z3_ast),ctx,i,t1)
end

@wrap function Z3_mk_ext_rotate_left(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_ext_rotate_left,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_ext_rotate_right(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_ext_rotate_right,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_int2bv(ctx::Z3_context,n::UInt32,t1::Z3_ast)
    ccall((:Z3_mk_int2bv,"libz3"),Z3_ast,(Z3_context,UInt32,Z3_ast),ctx,n,t1)
end

@wrap function Z3_mk_bv2int(ctx::Z3_context,t1::Z3_ast,is_signed::Z3_bool)
    ccall((:Z3_mk_bv2int,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_bool),ctx,t1,is_signed)
end

@wrap function Z3_mk_bvadd_no_overflow(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast,is_signed::Z3_bool)
    ccall((:Z3_mk_bvadd_no_overflow,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast,Z3_bool),ctx,t1,t2,is_signed)
end

@wrap function Z3_mk_bvadd_no_underflow(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvadd_no_underflow,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvsub_no_overflow(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsub_no_overflow,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvsub_no_underflow(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast,is_signed::Z3_bool)
    ccall((:Z3_mk_bvsub_no_underflow,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast,Z3_bool),ctx,t1,t2,is_signed)
end

@wrap function Z3_mk_bvsdiv_no_overflow(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsdiv_no_overflow,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_bvneg_no_overflow(ctx::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_bvneg_no_overflow,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,t1)
end

@wrap function Z3_mk_bvmul_no_overflow(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast,is_signed::Z3_bool)
    ccall((:Z3_mk_bvmul_no_overflow,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast,Z3_bool),ctx,t1,t2,is_signed)
end

@wrap function Z3_mk_bvmul_no_underflow(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvmul_no_underflow,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_mk_select(ctx::Z3_context,a::Z3_ast,i::Z3_ast)
    ccall((:Z3_mk_select,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,a,i)
end

@wrap function Z3_mk_store(ctx::Z3_context,a::Z3_ast,i::Z3_ast,v::Z3_ast)
    ccall((:Z3_mk_store,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast,Z3_ast),ctx,a,i,v)
end

@wrap function Z3_mk_const_array(ctx::Z3_context,domain::Z3_sort,v::Z3_ast)
    ccall((:Z3_mk_const_array,"libz3"),Z3_ast,(Z3_context,Z3_sort,Z3_ast),ctx,domain,v)
end

@wrap function Z3_mk_map(ctx::Z3_context,f::Z3_func_decl,n::UInt32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_map,"libz3"),Z3_ast,(Z3_context,Z3_func_decl,UInt32,Ptr{Z3_ast}),ctx,f,n,args)
end

@wrap function Z3_mk_array_default(ctx::Z3_context,array::Z3_ast)
    ccall((:Z3_mk_array_default,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,array)
end

@wrap function Z3_mk_set_sort(ctx::Z3_context,ty::Z3_sort)
    ccall((:Z3_mk_set_sort,"libz3"),Z3_sort,(Z3_context,Z3_sort),ctx,ty)
end

@wrap function Z3_mk_empty_set(ctx::Z3_context,domain::Z3_sort)
    ccall((:Z3_mk_empty_set,"libz3"),Z3_ast,(Z3_context,Z3_sort),ctx,domain)
end

@wrap function Z3_mk_full_set(ctx::Z3_context,domain::Z3_sort)
    ccall((:Z3_mk_full_set,"libz3"),Z3_ast,(Z3_context,Z3_sort),ctx,domain)
end

@wrap function Z3_mk_set_add(ctx::Z3_context,set::Z3_ast,elem::Z3_ast)
    ccall((:Z3_mk_set_add,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,set,elem)
end

@wrap function Z3_mk_set_del(ctx::Z3_context,set::Z3_ast,elem::Z3_ast)
    ccall((:Z3_mk_set_del,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,set,elem)
end

@wrap function Z3_mk_set_union(ctx::Z3_context,num_args::UInt32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_set_union,"libz3"),Z3_ast,(Z3_context,UInt32,Ptr{Z3_ast}),ctx,num_args,args)
end

@wrap function Z3_mk_set_intersect(ctx::Z3_context,num_args::UInt32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_set_intersect,"libz3"),Z3_ast,(Z3_context,UInt32,Ptr{Z3_ast}),ctx,num_args,args)
end

@wrap function Z3_mk_set_difference(ctx::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_set_difference,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,arg1,arg2)
end

@wrap function Z3_mk_set_complement(ctx::Z3_context,arg::Z3_ast)
    ccall((:Z3_mk_set_complement,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,arg)
end

@wrap function Z3_mk_set_member(ctx::Z3_context,elem::Z3_ast,set::Z3_ast)
    ccall((:Z3_mk_set_member,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,elem,set)
end

@wrap function Z3_mk_set_subset(ctx::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_set_subset,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,arg1,arg2)
end

@wrap function Z3_mk_numeral(ctx::Z3_context,numeral::Z3_string,ty::Z3_sort)
    ccall((:Z3_mk_numeral,"libz3"),Z3_ast,(Z3_context,Z3_string,Z3_sort),ctx,numeral,ty)
end

@wrap function Z3_mk_real(ctx::Z3_context,num::Cint,den::Cint)
    ccall((:Z3_mk_real,"libz3"),Z3_ast,(Z3_context,Cint,Cint),ctx,num,den)
end

@wrap function Z3_mk_int(ctx::Z3_context,v::Cint,ty::Z3_sort)
    ccall((:Z3_mk_int,"libz3"),Z3_ast,(Z3_context,Cint,Z3_sort),ctx,v,ty)
end

@wrap function Z3_mk_unsigned_int(ctx::Z3_context,v::UInt32,ty::Z3_sort)
    ccall((:Z3_mk_unsigned_int,"libz3"),Z3_ast,(Z3_context,UInt32,Z3_sort),ctx,v,ty)
end

@wrap function Z3_mk_int64(ctx::Z3_context,v::Clonglong,ty::Z3_sort)
    ccall((:Z3_mk_int64,"libz3"),Z3_ast,(Z3_context,Clonglong,Z3_sort),ctx,v,ty)
end

@wrap function Z3_mk_unsigned_int64(ctx::Z3_context,v::Culonglong,ty::Z3_sort)
    ccall((:Z3_mk_unsigned_int64,"libz3"),Z3_ast,(Z3_context,Culonglong,Z3_sort),ctx,v,ty)
end

@wrap function Z3_mk_pattern(ctx::Z3_context,num_patterns::UInt32,terms::Ptr{Z3_ast})
    ccall((:Z3_mk_pattern,"libz3"),Z3_pattern,(Z3_context,UInt32,Ptr{Z3_ast}),ctx,num_patterns,terms)
end

@wrap function Z3_mk_bound(ctx::Z3_context,index::UInt32,ty::Z3_sort)
    ccall((:Z3_mk_bound,"libz3"),Z3_ast,(Z3_context,UInt32,Z3_sort),ctx,index,ty)
end

@wrap function Z3_mk_forall(ctx::Z3_context,weight::UInt32,num_patterns::UInt32,patterns::Ptr{Z3_pattern},num_decls::UInt32,sorts::Ptr{Z3_sort},decl_names::Ptr{Z3_symbol},body::Z3_ast)
    ccall((:Z3_mk_forall,"libz3"),Z3_ast,(Z3_context,UInt32,UInt32,Ptr{Z3_pattern},UInt32,Ptr{Z3_sort},Ptr{Z3_symbol},Z3_ast),ctx,weight,num_patterns,patterns,num_decls,sorts,decl_names,body)
end

@wrap function Z3_mk_exists(ctx::Z3_context,weight::UInt32,num_patterns::UInt32,patterns::Ptr{Z3_pattern},num_decls::UInt32,sorts::Ptr{Z3_sort},decl_names::Ptr{Z3_symbol},body::Z3_ast)
    ccall((:Z3_mk_exists,"libz3"),Z3_ast,(Z3_context,UInt32,UInt32,Ptr{Z3_pattern},UInt32,Ptr{Z3_sort},Ptr{Z3_symbol},Z3_ast),ctx,weight,num_patterns,patterns,num_decls,sorts,decl_names,body)
end

@wrap function Z3_mk_quantifier(ctx::Z3_context,is_forall::Z3_bool,weight::UInt32,num_patterns::UInt32,patterns::Ptr{Z3_pattern},num_decls::UInt32,sorts::Ptr{Z3_sort},decl_names::Ptr{Z3_symbol},body::Z3_ast)
    ccall((:Z3_mk_quantifier,"libz3"),Z3_ast,(Z3_context,Z3_bool,UInt32,UInt32,Ptr{Z3_pattern},UInt32,Ptr{Z3_sort},Ptr{Z3_symbol},Z3_ast),ctx,is_forall,weight,num_patterns,patterns,num_decls,sorts,decl_names,body)
end

@wrap function Z3_mk_quantifier_ex(ctx::Z3_context,is_forall::Z3_bool,weight::UInt32,quantifier_id::Z3_symbol,skolem_id::Z3_symbol,num_patterns::UInt32,patterns::Ptr{Z3_pattern},num_no_patterns::UInt32,no_patterns::Ptr{Z3_ast},num_decls::UInt32,sorts::Ptr{Z3_sort},decl_names::Ptr{Z3_symbol},body::Z3_ast)
    ccall((:Z3_mk_quantifier_ex,"libz3"),Z3_ast,(Z3_context,Z3_bool,UInt32,Z3_symbol,Z3_symbol,UInt32,Ptr{Z3_pattern},UInt32,Ptr{Z3_ast},UInt32,Ptr{Z3_sort},Ptr{Z3_symbol},Z3_ast),ctx,is_forall,weight,quantifier_id,skolem_id,num_patterns,patterns,num_no_patterns,no_patterns,num_decls,sorts,decl_names,body)
end

@wrap function Z3_mk_forall_const(ctx::Z3_context,weight::UInt32,num_bound::UInt32,bound::Ptr{Z3_app},num_patterns::UInt32,patterns::Ptr{Z3_pattern},body::Z3_ast)
    ccall((:Z3_mk_forall_const,"libz3"),Z3_ast,(Z3_context,UInt32,UInt32,Ptr{Z3_app},UInt32,Ptr{Z3_pattern},Z3_ast),ctx,weight,num_bound,bound,num_patterns,patterns,body)
end

@wrap function Z3_mk_exists_const(ctx::Z3_context,weight::UInt32,num_bound::UInt32,bound::Ptr{Z3_app},num_patterns::UInt32,patterns::Ptr{Z3_pattern},body::Z3_ast)
    ccall((:Z3_mk_exists_const,"libz3"),Z3_ast,(Z3_context,UInt32,UInt32,Ptr{Z3_app},UInt32,Ptr{Z3_pattern},Z3_ast),ctx,weight,num_bound,bound,num_patterns,patterns,body)
end

@wrap function Z3_mk_quantifier_const(ctx::Z3_context,is_forall::Z3_bool,weight::UInt32,num_bound::UInt32,bound::Ptr{Z3_app},num_patterns::UInt32,patterns::Ptr{Z3_pattern},body::Z3_ast)
    ccall((:Z3_mk_quantifier_const,"libz3"),Z3_ast,(Z3_context,Z3_bool,UInt32,UInt32,Ptr{Z3_app},UInt32,Ptr{Z3_pattern},Z3_ast),ctx,is_forall,weight,num_bound,bound,num_patterns,patterns,body)
end

@wrap function Z3_mk_quantifier_const_ex(ctx::Z3_context,is_forall::Z3_bool,weight::UInt32,quantifier_id::Z3_symbol,skolem_id::Z3_symbol,num_bound::UInt32,bound::Ptr{Z3_app},num_patterns::UInt32,patterns::Ptr{Z3_pattern},num_no_patterns::UInt32,no_patterns::Ptr{Z3_ast},body::Z3_ast)
    ccall((:Z3_mk_quantifier_const_ex,"libz3"),Z3_ast,(Z3_context,Z3_bool,UInt32,Z3_symbol,Z3_symbol,UInt32,Ptr{Z3_app},UInt32,Ptr{Z3_pattern},UInt32,Ptr{Z3_ast},Z3_ast),ctx,is_forall,weight,quantifier_id,skolem_id,num_bound,bound,num_patterns,patterns,num_no_patterns,no_patterns,body)
end

@wrap function Z3_get_symbol_kind(ctx::Z3_context,s::Z3_symbol)
    ccall((:Z3_get_symbol_kind,"libz3"),Z3_symbol_kind,(Z3_context,Z3_symbol),ctx,s)
end

@wrap function Z3_get_symbol_int(ctx::Z3_context,s::Z3_symbol)
    ccall((:Z3_get_symbol_int,"libz3"),Cint,(Z3_context,Z3_symbol),ctx,s)
end

@wrap function Z3_get_symbol_string(ctx::Z3_context,s::Z3_symbol)
    ccall((:Z3_get_symbol_string,"libz3"),Z3_string,(Z3_context,Z3_symbol),ctx,s)
end

@wrap function Z3_get_sort_name(ctx::Z3_context,d::Z3_sort)
    ccall((:Z3_get_sort_name,"libz3"),Z3_symbol,(Z3_context,Z3_sort),ctx,d)
end

@wrap function Z3_get_sort_id(ctx::Z3_context,s::Z3_sort)
    ccall((:Z3_get_sort_id,"libz3"),UInt32,(Z3_context,Z3_sort),ctx,s)
end

@wrap function Z3_sort_to_ast(ctx::Z3_context,s::Z3_sort)
    ccall((:Z3_sort_to_ast,"libz3"),Z3_ast,(Z3_context,Z3_sort),ctx,s)
end

@wrap function Z3_is_eq_sort(ctx::Z3_context,s1::Z3_sort,s2::Z3_sort)
    ccall((:Z3_is_eq_sort,"libz3"),Z3_bool,(Z3_context,Z3_sort,Z3_sort),ctx,s1,s2)
end

@wrap function Z3_get_sort_kind(ctx::Z3_context,t::Z3_sort)
    ccall((:Z3_get_sort_kind,"libz3"),Z3_sort_kind,(Z3_context,Z3_sort),ctx,t)
end

@wrap function Z3_get_bv_sort_size(ctx::Z3_context,t::Z3_sort)
    ccall((:Z3_get_bv_sort_size,"libz3"),UInt32,(Z3_context,Z3_sort),ctx,t)
end

@wrap function Z3_get_finite_domain_sort_size(ctx::Z3_context,s::Z3_sort,r::Ptr{Culonglong})
    ccall((:Z3_get_finite_domain_sort_size,"libz3"),Z3_bool,(Z3_context,Z3_sort,Ptr{Culonglong}),ctx,s,r)
end

@wrap function Z3_get_array_sort_domain(ctx::Z3_context,t::Z3_sort)
    ccall((:Z3_get_array_sort_domain,"libz3"),Z3_sort,(Z3_context,Z3_sort),ctx,t)
end

@wrap function Z3_get_array_sort_range(ctx::Z3_context,t::Z3_sort)
    ccall((:Z3_get_array_sort_range,"libz3"),Z3_sort,(Z3_context,Z3_sort),ctx,t)
end

@wrap function Z3_get_tuple_sort_mk_decl(ctx::Z3_context,t::Z3_sort)
    ccall((:Z3_get_tuple_sort_mk_decl,"libz3"),Z3_func_decl,(Z3_context,Z3_sort),ctx,t)
end

@wrap function Z3_get_tuple_sort_num_fields(ctx::Z3_context,t::Z3_sort)
    ccall((:Z3_get_tuple_sort_num_fields,"libz3"),UInt32,(Z3_context,Z3_sort),ctx,t)
end

@wrap function Z3_get_tuple_sort_field_decl(ctx::Z3_context,t::Z3_sort,i::UInt32)
    ccall((:Z3_get_tuple_sort_field_decl,"libz3"),Z3_func_decl,(Z3_context,Z3_sort,UInt32),ctx,t,i)
end

@wrap function Z3_get_datatype_sort_num_constructors(ctx::Z3_context,t::Z3_sort)
    ccall((:Z3_get_datatype_sort_num_constructors,"libz3"),UInt32,(Z3_context,Z3_sort),ctx,t)
end

@wrap function Z3_get_datatype_sort_constructor(ctx::Z3_context,t::Z3_sort,idx::UInt32)
    ccall((:Z3_get_datatype_sort_constructor,"libz3"),Z3_func_decl,(Z3_context,Z3_sort,UInt32),ctx,t,idx)
end

@wrap function Z3_get_datatype_sort_recognizer(ctx::Z3_context,t::Z3_sort,idx::UInt32)
    ccall((:Z3_get_datatype_sort_recognizer,"libz3"),Z3_func_decl,(Z3_context,Z3_sort,UInt32),ctx,t,idx)
end

@wrap function Z3_get_datatype_sort_constructor_accessor(ctx::Z3_context,t::Z3_sort,idx_c::UInt32,idx_a::UInt32)
    ccall((:Z3_get_datatype_sort_constructor_accessor,"libz3"),Z3_func_decl,(Z3_context,Z3_sort,UInt32,UInt32),ctx,t,idx_c,idx_a)
end

@wrap function Z3_get_relation_arity(ctx::Z3_context,s::Z3_sort)
    ccall((:Z3_get_relation_arity,"libz3"),UInt32,(Z3_context,Z3_sort),ctx,s)
end

@wrap function Z3_get_relation_column(ctx::Z3_context,s::Z3_sort,ctxol::UInt32)
    ccall((:Z3_get_relation_column,"libz3"),Z3_sort,(Z3_context,Z3_sort,UInt32),ctx,s,ctxol)
end

@wrap function Z3_func_decl_to_ast(ctx::Z3_context,f::Z3_func_decl)
    ccall((:Z3_func_decl_to_ast,"libz3"),Z3_ast,(Z3_context,Z3_func_decl),ctx,f)
end

@wrap function Z3_is_eq_func_decl(ctx::Z3_context,f1::Z3_func_decl,f2::Z3_func_decl)
    ccall((:Z3_is_eq_func_decl,"libz3"),Z3_bool,(Z3_context,Z3_func_decl,Z3_func_decl),ctx,f1,f2)
end

@wrap function Z3_get_func_decl_id(ctx::Z3_context,f::Z3_func_decl)
    ccall((:Z3_get_func_decl_id,"libz3"),UInt32,(Z3_context,Z3_func_decl),ctx,f)
end

@wrap function Z3_get_decl_name(ctx::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_decl_name,"libz3"),Z3_symbol,(Z3_context,Z3_func_decl),ctx,d)
end

@wrap function Z3_get_decl_kind(ctx::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_decl_kind,"libz3"),Z3_decl_kind,(Z3_context,Z3_func_decl),ctx,d)
end

@wrap function Z3_get_domain_size(ctx::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_domain_size,"libz3"),UInt32,(Z3_context,Z3_func_decl),ctx,d)
end

@wrap function Z3_get_arity(ctx::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_arity,"libz3"),UInt32,(Z3_context,Z3_func_decl),ctx,d)
end

@wrap function Z3_get_domain(ctx::Z3_context,d::Z3_func_decl,i::UInt32)
    ccall((:Z3_get_domain,"libz3"),Z3_sort,(Z3_context,Z3_func_decl,UInt32),ctx,d,i)
end

@wrap function Z3_get_range(ctx::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_range,"libz3"),Z3_sort,(Z3_context,Z3_func_decl),ctx,d)
end

@wrap function Z3_get_decl_num_parameters(ctx::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_decl_num_parameters,"libz3"),UInt32,(Z3_context,Z3_func_decl),ctx,d)
end

@wrap function Z3_get_decl_parameter_kind(ctx::Z3_context,d::Z3_func_decl,idx::UInt32)
    ccall((:Z3_get_decl_parameter_kind,"libz3"),Z3_parameter_kind,(Z3_context,Z3_func_decl,UInt32),ctx,d,idx)
end

@wrap function Z3_get_decl_int_parameter(ctx::Z3_context,d::Z3_func_decl,idx::UInt32)
    ccall((:Z3_get_decl_int_parameter,"libz3"),Cint,(Z3_context,Z3_func_decl,UInt32),ctx,d,idx)
end

@wrap function Z3_get_decl_double_parameter(ctx::Z3_context,d::Z3_func_decl,idx::UInt32)
    ccall((:Z3_get_decl_double_parameter,"libz3"),Cdouble,(Z3_context,Z3_func_decl,UInt32),ctx,d,idx)
end

@wrap function Z3_get_decl_symbol_parameter(ctx::Z3_context,d::Z3_func_decl,idx::UInt32)
    ccall((:Z3_get_decl_symbol_parameter,"libz3"),Z3_symbol,(Z3_context,Z3_func_decl,UInt32),ctx,d,idx)
end

@wrap function Z3_get_decl_sort_parameter(ctx::Z3_context,d::Z3_func_decl,idx::UInt32)
    ccall((:Z3_get_decl_sort_parameter,"libz3"),Z3_sort,(Z3_context,Z3_func_decl,UInt32),ctx,d,idx)
end

@wrap function Z3_get_decl_ast_parameter(ctx::Z3_context,d::Z3_func_decl,idx::UInt32)
    ccall((:Z3_get_decl_ast_parameter,"libz3"),Z3_ast,(Z3_context,Z3_func_decl,UInt32),ctx,d,idx)
end

@wrap function Z3_get_decl_func_decl_parameter(ctx::Z3_context,d::Z3_func_decl,idx::UInt32)
    ccall((:Z3_get_decl_func_decl_parameter,"libz3"),Z3_func_decl,(Z3_context,Z3_func_decl,UInt32),ctx,d,idx)
end

@wrap function Z3_get_decl_rational_parameter(ctx::Z3_context,d::Z3_func_decl,idx::UInt32)
    ccall((:Z3_get_decl_rational_parameter,"libz3"),Z3_string,(Z3_context,Z3_func_decl,UInt32),ctx,d,idx)
end

@wrap function Z3_app_to_ast(ctx::Z3_context,a::Z3_app)
    ccall((:Z3_app_to_ast,"libz3"),Z3_ast,(Z3_context,Z3_app),ctx,a)
end

@wrap function Z3_get_app_decl(ctx::Z3_context,a::Z3_app)
    ccall((:Z3_get_app_decl,"libz3"),Z3_func_decl,(Z3_context,Z3_app),ctx,a)
end

@wrap function Z3_get_app_num_args(ctx::Z3_context,a::Z3_app)
    ccall((:Z3_get_app_num_args,"libz3"),UInt32,(Z3_context,Z3_app),ctx,a)
end

@wrap function Z3_get_app_arg(ctx::Z3_context,a::Z3_app,i::UInt32)
    ccall((:Z3_get_app_arg,"libz3"),Z3_ast,(Z3_context,Z3_app,UInt32),ctx,a,i)
end

@wrap function Z3_is_eq_ast(ctx::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_is_eq_ast,"libz3"),Z3_bool,(Z3_context,Z3_ast,Z3_ast),ctx,t1,t2)
end

@wrap function Z3_get_ast_id(ctx::Z3_context,t::Z3_ast)
    ccall((:Z3_get_ast_id,"libz3"),UInt32,(Z3_context,Z3_ast),ctx,t)
end

@wrap function Z3_get_ast_hash(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_ast_hash,"libz3"),UInt32,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_sort(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_sort,"libz3"),Z3_sort,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_is_well_sorted(ctx::Z3_context,t::Z3_ast)
    ccall((:Z3_is_well_sorted,"libz3"),Z3_bool,(Z3_context,Z3_ast),ctx,t)
end

@wrap function Z3_get_bool_value(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_bool_value,"libz3"),Z3_lbool,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_ast_kind(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_ast_kind,"libz3"),Z3_ast_kind,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_is_app(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_is_app,"libz3"),Z3_bool,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_is_numeral_ast(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_is_numeral_ast,"libz3"),Z3_bool,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_is_algebraic_number(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_is_algebraic_number,"libz3"),Z3_bool,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_to_app(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_to_app,"libz3"),Z3_app,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_to_func_decl(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_to_func_decl,"libz3"),Z3_func_decl,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_numeral_string(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_numeral_string,"libz3"),Z3_string,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_numeral_decimal_string(ctx::Z3_context,a::Z3_ast,precision::UInt32)
    ccall((:Z3_get_numeral_decimal_string,"libz3"),Z3_string,(Z3_context,Z3_ast,UInt32),ctx,a,precision)
end

@wrap function Z3_get_numerator(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_numerator,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_denominator(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_denominator,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_numeral_small(ctx::Z3_context,a::Z3_ast,num::Ref{Clonglong},den::Ref{Clonglong})
    ccall((:Z3_get_numeral_small,"libz3"),Z3_bool,(Z3_context,Z3_ast,Ref{Clonglong},Ref{Clonglong}),ctx,a,num,den)
end

@wrap function Z3_get_numeral_int(ctx::Z3_context,v::Z3_ast,i::Ref{Cint})
    ccall((:Z3_get_numeral_int,"libz3"),Z3_bool,(Z3_context,Z3_ast,Ref{Cint}),ctx,v,i)
end

@wrap function Z3_get_numeral_uint(ctx::Z3_context,v::Z3_ast,u::Ref{UInt32})
    ccall((:Z3_get_numeral_uint,"libz3"),Z3_bool,(Z3_context,Z3_ast,Ref{UInt32}),ctx,v,u)
end

@wrap function Z3_get_numeral_uint64(ctx::Z3_context,v::Z3_ast,u::Ptr{Culonglong})
    ccall((:Z3_get_numeral_uint64,"libz3"),Z3_bool,(Z3_context,Z3_ast,Ptr{Culonglong}),ctx,v,u)
end

#FIXME: Do I need to modify the others
@wrap function Z3_get_numeral_int64(ctx::Z3_context,v::Z3_ast,i::Ref{Clonglong})
    ccall((:Z3_get_numeral_int64,"libz3"),Z3_bool,(Z3_context,Z3_ast,Ref{Clonglong}),ctx,v,i)
end

@wrap function Z3_get_numeral_rational_int64(ctx::Z3_context,v::Z3_ast,num::Ref{Clonglong},den::Ref{Clonglong})
    ccall((:Z3_get_numeral_rational_int64,"libz3"),Z3_bool,(Z3_context,Z3_ast,Ref{Clonglong},Ref{Clonglong}),ctx,v,num,den)
end

@wrap function Z3_get_algebraic_number_lower(ctx::Z3_context,a::Z3_ast,precision::UInt32)
    ccall((:Z3_get_algebraic_number_lower,"libz3"),Z3_ast,(Z3_context,Z3_ast,UInt32),ctx,a,precision)
end

@wrap function Z3_get_algebraic_number_upper(ctx::Z3_context,a::Z3_ast,precision::UInt32)
    ccall((:Z3_get_algebraic_number_upper,"libz3"),Z3_ast,(Z3_context,Z3_ast,UInt32),ctx,a,precision)
end

@wrap function Z3_pattern_to_ast(ctx::Z3_context,p::Z3_pattern)
    ccall((:Z3_pattern_to_ast,"libz3"),Z3_ast,(Z3_context,Z3_pattern),ctx,p)
end

@wrap function Z3_get_pattern_num_terms(ctx::Z3_context,p::Z3_pattern)
    ccall((:Z3_get_pattern_num_terms,"libz3"),UInt32,(Z3_context,Z3_pattern),ctx,p)
end

@wrap function Z3_get_pattern(ctx::Z3_context,p::Z3_pattern,idx::UInt32)
    ccall((:Z3_get_pattern,"libz3"),Z3_ast,(Z3_context,Z3_pattern,UInt32),ctx,p,idx)
end

@wrap function Z3_get_index_value(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_index_value,"libz3"),UInt32,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_is_quantifier_forall(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_is_quantifier_forall,"libz3"),Z3_bool,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_quantifier_weight(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_quantifier_weight,"libz3"),UInt32,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_quantifier_num_patterns(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_quantifier_num_patterns,"libz3"),UInt32,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_quantifier_pattern_ast(ctx::Z3_context,a::Z3_ast,i::UInt32)
    ccall((:Z3_get_quantifier_pattern_ast,"libz3"),Z3_pattern,(Z3_context,Z3_ast,UInt32),ctx,a,i)
end

@wrap function Z3_get_quantifier_num_no_patterns(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_quantifier_num_no_patterns,"libz3"),UInt32,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_quantifier_no_pattern_ast(ctx::Z3_context,a::Z3_ast,i::UInt32)
    ccall((:Z3_get_quantifier_no_pattern_ast,"libz3"),Z3_ast,(Z3_context,Z3_ast,UInt32),ctx,a,i)
end

@wrap function Z3_get_quantifier_num_bound(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_quantifier_num_bound,"libz3"),UInt32,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_quantifier_bound_name(ctx::Z3_context,a::Z3_ast,i::UInt32)
    ccall((:Z3_get_quantifier_bound_name,"libz3"),Z3_symbol,(Z3_context,Z3_ast,UInt32),ctx,a,i)
end

@wrap function Z3_get_quantifier_bound_sort(ctx::Z3_context,a::Z3_ast,i::UInt32)
    ccall((:Z3_get_quantifier_bound_sort,"libz3"),Z3_sort,(Z3_context,Z3_ast,UInt32),ctx,a,i)
end

@wrap function Z3_get_quantifier_body(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_quantifier_body,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_simplify(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_simplify,"libz3"),Z3_ast,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_simplify_ex(ctx::Z3_context,a::Z3_ast,p::Z3_params)
    ccall((:Z3_simplify_ex,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_params),ctx,a,p)
end

@wrap function Z3_simplify_get_help(ctx::Z3_context)
    ccall((:Z3_simplify_get_help,"libz3"),Z3_string,(Z3_context,),ctx)
end

@wrap function Z3_simplify_get_param_descrs(ctx::Z3_context)
    ccall((:Z3_simplify_get_param_descrs,"libz3"),Z3_param_descrs,(Z3_context,),ctx)
end

@wrap function Z3_update_term(ctx::Z3_context,a::Z3_ast,num_args::UInt32,args::Ptr{Z3_ast})
    ccall((:Z3_update_term,"libz3"),Z3_ast,(Z3_context,Z3_ast,UInt32,Ptr{Z3_ast}),ctx,a,num_args,args)
end

@wrap function Z3_substitute(ctx::Z3_context,a::Z3_ast,num_exprs::UInt32,from::Ptr{Z3_ast},to::Ptr{Z3_ast})
    ccall((:Z3_substitute,"libz3"),Z3_ast,(Z3_context,Z3_ast,UInt32,Ptr{Z3_ast},Ptr{Z3_ast}),ctx,a,num_exprs,from,to)
end

@wrap function Z3_substitute_vars(ctx::Z3_context,a::Z3_ast,num_exprs::UInt32,to::Ptr{Z3_ast})
    ccall((:Z3_substitute_vars,"libz3"),Z3_ast,(Z3_context,Z3_ast,UInt32,Ptr{Z3_ast}),ctx,a,num_exprs,to)
end

@wrap function Z3_translate(source::Z3_context,a::Z3_ast,target::Z3_context)
    ccall((:Z3_translate,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_context),source,a,target)
end

@wrap function Z3_model_inc_ref(ctx::Z3_context,m::Z3_model)
    ccall((:Z3_model_inc_ref,"libz3"),Void,(Z3_context,Z3_model),ctx,m)
end

@wrap function Z3_model_dec_ref(ctx::Z3_context,m::Z3_model)
    ccall((:Z3_model_dec_ref,"libz3"),Void,(Z3_context,Z3_model),ctx,m)
end

@wrap function Z3_model_eval(ctx::Z3_context,m::Z3_model,t::Z3_ast,model_completion::Z3_bool,v::Ptr{Z3_ast})
    ccall((:Z3_model_eval,"libz3"),Z3_bool,(Z3_context,Z3_model,Z3_ast,Z3_bool,Ptr{Z3_ast}),ctx,m,t,model_completion,v)
end

@wrap function Z3_model_get_const_interp(ctx::Z3_context,m::Z3_model,a::Z3_func_decl)
    ccall((:Z3_model_get_const_interp,"libz3"),Z3_ast,(Z3_context,Z3_model,Z3_func_decl),ctx,m,a)
end

@wrap function Z3_model_has_interp(ctx::Z3_context,m::Z3_model,a::Z3_func_decl)
    ccall((:Z3_model_has_interp,"libz3"),Z3_bool,(Z3_context,Z3_model,Z3_func_decl),ctx,m,a)
end

@wrap function Z3_model_get_func_interp(ctx::Z3_context,m::Z3_model,f::Z3_func_decl)
    ccall((:Z3_model_get_func_interp,"libz3"),Z3_func_interp,(Z3_context,Z3_model,Z3_func_decl),ctx,m,f)
end

@wrap function Z3_model_get_num_consts(ctx::Z3_context,m::Z3_model)
    ccall((:Z3_model_get_num_consts,"libz3"),UInt32,(Z3_context,Z3_model),ctx,m)
end

@wrap function Z3_model_get_const_decl(ctx::Z3_context,m::Z3_model,i::UInt32)
    ccall((:Z3_model_get_const_decl,"libz3"),Z3_func_decl,(Z3_context,Z3_model,UInt32),ctx,m,i)
end

@wrap function Z3_model_get_num_funcs(ctx::Z3_context,m::Z3_model)
    ccall((:Z3_model_get_num_funcs,"libz3"),UInt32,(Z3_context,Z3_model),ctx,m)
end

@wrap function Z3_model_get_func_decl(ctx::Z3_context,m::Z3_model,i::UInt32)
    ccall((:Z3_model_get_func_decl,"libz3"),Z3_func_decl,(Z3_context,Z3_model,UInt32),ctx,m,i)
end

@wrap function Z3_model_get_num_sorts(ctx::Z3_context,m::Z3_model)
    ccall((:Z3_model_get_num_sorts,"libz3"),UInt32,(Z3_context,Z3_model),ctx,m)
end

@wrap function Z3_model_get_sort(ctx::Z3_context,m::Z3_model,i::UInt32)
    ccall((:Z3_model_get_sort,"libz3"),Z3_sort,(Z3_context,Z3_model,UInt32),ctx,m,i)
end

@wrap function Z3_model_get_sort_universe(ctx::Z3_context,m::Z3_model,s::Z3_sort)
    ccall((:Z3_model_get_sort_universe,"libz3"),Z3_ast_vector,(Z3_context,Z3_model,Z3_sort),ctx,m,s)
end

@wrap function Z3_is_as_array(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_is_as_array,"libz3"),Z3_bool,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_get_as_array_func_decl(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_get_as_array_func_decl,"libz3"),Z3_func_decl,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_func_interp_inc_ref(ctx::Z3_context,f::Z3_func_interp)
    ccall((:Z3_func_interp_inc_ref,"libz3"),Void,(Z3_context,Z3_func_interp),ctx,f)
end

@wrap function Z3_func_interp_dec_ref(ctx::Z3_context,f::Z3_func_interp)
    ccall((:Z3_func_interp_dec_ref,"libz3"),Void,(Z3_context,Z3_func_interp),ctx,f)
end

@wrap function Z3_func_interp_get_num_entries(ctx::Z3_context,f::Z3_func_interp)
    ccall((:Z3_func_interp_get_num_entries,"libz3"),UInt32,(Z3_context,Z3_func_interp),ctx,f)
end

@wrap function Z3_func_interp_get_entry(ctx::Z3_context,f::Z3_func_interp,i::UInt32)
    ccall((:Z3_func_interp_get_entry,"libz3"),Z3_func_entry,(Z3_context,Z3_func_interp,UInt32),ctx,f,i)
end

@wrap function Z3_func_interp_get_else(ctx::Z3_context,f::Z3_func_interp)
    ccall((:Z3_func_interp_get_else,"libz3"),Z3_ast,(Z3_context,Z3_func_interp),ctx,f)
end

@wrap function Z3_func_interp_get_arity(ctx::Z3_context,f::Z3_func_interp)
    ccall((:Z3_func_interp_get_arity,"libz3"),UInt32,(Z3_context,Z3_func_interp),ctx,f)
end

@wrap function Z3_func_entry_inc_ref(ctx::Z3_context,e::Z3_func_entry)
    ccall((:Z3_func_entry_inc_ref,"libz3"),Void,(Z3_context,Z3_func_entry),ctx,e)
end

@wrap function Z3_func_entry_dec_ref(ctx::Z3_context,e::Z3_func_entry)
    ccall((:Z3_func_entry_dec_ref,"libz3"),Void,(Z3_context,Z3_func_entry),ctx,e)
end

@wrap function Z3_func_entry_get_value(ctx::Z3_context,e::Z3_func_entry)
    ccall((:Z3_func_entry_get_value,"libz3"),Z3_ast,(Z3_context,Z3_func_entry),ctx,e)
end

@wrap function Z3_func_entry_get_num_args(ctx::Z3_context,e::Z3_func_entry)
    ccall((:Z3_func_entry_get_num_args,"libz3"),UInt32,(Z3_context,Z3_func_entry),ctx,e)
end

@wrap function Z3_func_entry_get_arg(ctx::Z3_context,e::Z3_func_entry,i::UInt32)
    ccall((:Z3_func_entry_get_arg,"libz3"),Z3_ast,(Z3_context,Z3_func_entry,UInt32),ctx,e,i)
end

@wrap function Z3_open_log(filename::Z3_string)
    ccall((:Z3_open_log,"libz3"),Z3_bool,(Z3_string,),filename)
end

@wrap function Z3_append_log(string::Z3_string)
    ccall((:Z3_append_log,"libz3"),Void,(Z3_string,),string)
end

@wrap function Z3_close_log()
    ccall((:Z3_close_log,"libz3"),Void,())
end

@wrap function Z3_toggle_warning_messages(enabled::Z3_bool)
    ccall((:Z3_toggle_warning_messages,"libz3"),Void,(Z3_bool,),enabled)
end

@wrap function Z3_set_ast_print_mode(ctx::Z3_context,mode::Z3_ast_print_mode)
    ccall((:Z3_set_ast_print_mode,"libz3"),Void,(Z3_context,Z3_ast_print_mode),ctx,mode)
end

@wrap function Z3_ast_to_string(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_ast_to_string,"libz3"),Z3_string,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_pattern_to_string(ctx::Z3_context,p::Z3_pattern)
    ccall((:Z3_pattern_to_string,"libz3"),Z3_string,(Z3_context,Z3_pattern),ctx,p)
end

@wrap function Z3_sort_to_string(ctx::Z3_context,s::Z3_sort)
    ccall((:Z3_sort_to_string,"libz3"),Z3_string,(Z3_context,Z3_sort),ctx,s)
end

@wrap function Z3_func_decl_to_string(ctx::Z3_context,d::Z3_func_decl)
    ccall((:Z3_func_decl_to_string,"libz3"),Z3_string,(Z3_context,Z3_func_decl),ctx,d)
end

@wrap function Z3_model_to_string(ctx::Z3_context,m::Z3_model)
    ccall((:Z3_model_to_string,"libz3"),Z3_string,(Z3_context,Z3_model),ctx,m)
end

@wrap function Z3_benchmark_to_smtlib_string(ctx::Z3_context,name::Z3_string,logic::Z3_string,status::Z3_string,attributes::Z3_string,num_assumptions::UInt32,assumptions::Ptr{Z3_ast},formula::Z3_ast)
    ccall((:Z3_benchmark_to_smtlib_string,"libz3"),Z3_string,(Z3_context,Z3_string,Z3_string,Z3_string,Z3_string,UInt32,Ptr{Z3_ast},Z3_ast),ctx,name,logic,status,attributes,num_assumptions,assumptions,formula)
end

@wrap function Z3_parse_smtlib2_string(ctx::Z3_context,str::Z3_string,num_sorts::UInt32,sort_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},num_decls::UInt32,decl_names::Ptr{Z3_symbol},decls::Ptr{Z3_func_decl})
    ccall((:Z3_parse_smtlib2_string,"libz3"),Z3_ast,(Z3_context,Z3_string,UInt32,Ptr{Z3_symbol},Ptr{Z3_sort},UInt32,Ptr{Z3_symbol},Ptr{Z3_func_decl}),ctx,str,num_sorts,sort_names,sorts,num_decls,decl_names,decls)
end

@wrap function Z3_parse_smtlib2_file(ctx::Z3_context,file_name::Z3_string,num_sorts::UInt32,sort_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},num_decls::UInt32,decl_names::Ptr{Z3_symbol},decls::Ptr{Z3_func_decl})
    ccall((:Z3_parse_smtlib2_file,"libz3"),Z3_ast,(Z3_context,Z3_string,UInt32,Ptr{Z3_symbol},Ptr{Z3_sort},UInt32,Ptr{Z3_symbol},Ptr{Z3_func_decl}),ctx,file_name,num_sorts,sort_names,sorts,num_decls,decl_names,decls)
end

@wrap function Z3_parse_smtlib_string(ctx::Z3_context,str::Z3_string,num_sorts::UInt32,sort_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},num_decls::UInt32,decl_names::Ptr{Z3_symbol},decls::Ptr{Z3_func_decl})
    ccall((:Z3_parse_smtlib_string,"libz3"),Void,(Z3_context,Z3_string,UInt32,Ptr{Z3_symbol},Ptr{Z3_sort},UInt32,Ptr{Z3_symbol},Ptr{Z3_func_decl}),ctx,str,num_sorts,sort_names,sorts,num_decls,decl_names,decls)
end

@wrap function Z3_parse_smtlib_file(ctx::Z3_context,file_name::Z3_string,num_sorts::UInt32,sort_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},num_decls::UInt32,decl_names::Ptr{Z3_symbol},decls::Ptr{Z3_func_decl})
    ccall((:Z3_parse_smtlib_file,"libz3"),Void,(Z3_context,Z3_string,UInt32,Ptr{Z3_symbol},Ptr{Z3_sort},UInt32,Ptr{Z3_symbol},Ptr{Z3_func_decl}),ctx,file_name,num_sorts,sort_names,sorts,num_decls,decl_names,decls)
end

@wrap function Z3_get_smtlib_num_formulas(ctx::Z3_context)
    ccall((:Z3_get_smtlib_num_formulas,"libz3"),UInt32,(Z3_context,),ctx)
end

@wrap function Z3_get_smtlib_formula(ctx::Z3_context,i::UInt32)
    ccall((:Z3_get_smtlib_formula,"libz3"),Z3_ast,(Z3_context,UInt32),ctx,i)
end

@wrap function Z3_get_smtlib_num_assumptions(ctx::Z3_context)
    ccall((:Z3_get_smtlib_num_assumptions,"libz3"),UInt32,(Z3_context,),ctx)
end

@wrap function Z3_get_smtlib_assumption(ctx::Z3_context,i::UInt32)
    ccall((:Z3_get_smtlib_assumption,"libz3"),Z3_ast,(Z3_context,UInt32),ctx,i)
end

@wrap function Z3_get_smtlib_num_decls(ctx::Z3_context)
    ccall((:Z3_get_smtlib_num_decls,"libz3"),UInt32,(Z3_context,),ctx)
end

@wrap function Z3_get_smtlib_decl(ctx::Z3_context,i::UInt32)
    ccall((:Z3_get_smtlib_decl,"libz3"),Z3_func_decl,(Z3_context,UInt32),ctx,i)
end

@wrap function Z3_get_smtlib_num_sorts(ctx::Z3_context)
    ccall((:Z3_get_smtlib_num_sorts,"libz3"),UInt32,(Z3_context,),ctx)
end

@wrap function Z3_get_smtlib_sort(ctx::Z3_context,i::UInt32)
    ccall((:Z3_get_smtlib_sort,"libz3"),Z3_sort,(Z3_context,UInt32),ctx,i)
end

@wrap function Z3_get_smtlib_error(ctx::Z3_context)
    ccall((:Z3_get_smtlib_error,"libz3"),Z3_string,(Z3_context,),ctx)
end

@wrap function Z3_get_error_code(ctx::Z3_context)
    ccall((:Z3_get_error_code,"libz3"),Z3_error_code,(Z3_context,),ctx)
end

@wrap function Z3_set_error_handler(ctx::Z3_context,h::Z3_error_handler)
    ccall((:Z3_set_error_handler,"libz3"),Void,(Z3_context,Z3_error_handler),ctx,h)
end

@wrap function Z3_set_error(ctx::Z3_context,e::Z3_error_code)
    ccall((:Z3_set_error,"libz3"),Void,(Z3_context,Z3_error_code),ctx,e)
end

@wrap function Z3_get_error_msg(err::Z3_error_code)
    ccall((:Z3_get_error_msg,"libz3"),Z3_string,(Z3_error_code,),err)
end

@wrap function Z3_get_error_msg_ex(ctx::Z3_context,err::Z3_error_code)
    ccall((:Z3_get_error_msg_ex,"libz3"),Z3_string,(Z3_context,Z3_error_code),ctx,err)
end

@wrap function Z3_get_version(major::Ref{UInt32},minor::Ref{UInt32},build_number::Ref{UInt32},revision_number::Ref{UInt32})
    ccall((:Z3_get_version,"libz3"),Void,(Ref{UInt32},Ref{UInt32},Ref{UInt32},Ref{UInt32}),major,minor,build_number,revision_number)
end

@wrap function Z3_enable_trace(tag::Z3_string)
    ccall((:Z3_enable_trace,"libz3"),Void,(Z3_string,),tag)
end

@wrap function Z3_disable_trace(tag::Z3_string)
    ccall((:Z3_disable_trace,"libz3"),Void,(Z3_string,),tag)
end

@wrap function Z3_reset_memory()
    ccall((:Z3_reset_memory,"libz3"),Void,())
end

@wrap function Z3_mk_theory(ctx::Z3_context,th_name::Z3_string,data::Z3_theory_data)
    ccall((:Z3_mk_theory,"libz3"),Z3_theory,(Z3_context,Z3_string,Z3_theory_data),ctx,th_name,data)
end

@wrap function Z3_theory_get_ext_data(t::Z3_theory)
    ccall((:Z3_theory_get_ext_data,"libz3"),Z3_theory_data,(Z3_theory,),t)
end

@wrap function Z3_theory_mk_sort(ctx::Z3_context,t::Z3_theory,s::Z3_symbol)
    ccall((:Z3_theory_mk_sort,"libz3"),Z3_sort,(Z3_context,Z3_theory,Z3_symbol),ctx,t,s)
end

@wrap function Z3_theory_mk_value(ctx::Z3_context,t::Z3_theory,n::Z3_symbol,s::Z3_sort)
    ccall((:Z3_theory_mk_value,"libz3"),Z3_ast,(Z3_context,Z3_theory,Z3_symbol,Z3_sort),ctx,t,n,s)
end

@wrap function Z3_theory_mk_constant(ctx::Z3_context,t::Z3_theory,n::Z3_symbol,s::Z3_sort)
    ccall((:Z3_theory_mk_constant,"libz3"),Z3_ast,(Z3_context,Z3_theory,Z3_symbol,Z3_sort),ctx,t,n,s)
end

@wrap function Z3_theory_mk_func_decl(ctx::Z3_context,t::Z3_theory,n::Z3_symbol,domain_size::UInt32,domain::Ptr{Z3_sort},range::Z3_sort)
    ccall((:Z3_theory_mk_func_decl,"libz3"),Z3_func_decl,(Z3_context,Z3_theory,Z3_symbol,UInt32,Ptr{Z3_sort},Z3_sort),ctx,t,n,domain_size,domain,range)
end

@wrap function Z3_theory_get_context(t::Z3_theory)
    ccall((:Z3_theory_get_context,"libz3"),Z3_context,(Z3_theory,),t)
end

@wrap function Z3_set_delete_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_delete_callback,"libz3"),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

@wrap function Z3_set_reduce_app_callback(t::Z3_theory,f::Z3_reduce_app_callback_fptr)
    ccall((:Z3_set_reduce_app_callback,"libz3"),Void,(Z3_theory,Z3_reduce_app_callback_fptr),t,f)
end

@wrap function Z3_set_reduce_eq_callback(t::Z3_theory,f::Z3_reduce_eq_callback_fptr)
    ccall((:Z3_set_reduce_eq_callback,"libz3"),Void,(Z3_theory,Z3_reduce_eq_callback_fptr),t,f)
end

@wrap function Z3_set_reduce_distinct_callback(t::Z3_theory,f::Z3_reduce_distinct_callback_fptr)
    ccall((:Z3_set_reduce_distinct_callback,"libz3"),Void,(Z3_theory,Z3_reduce_distinct_callback_fptr),t,f)
end

@wrap function Z3_set_new_app_callback(t::Z3_theory,f::Z3_theory_ast_callback_fptr)
    ccall((:Z3_set_new_app_callback,"libz3"),Void,(Z3_theory,Z3_theory_ast_callback_fptr),t,f)
end

@wrap function Z3_set_new_elem_callback(t::Z3_theory,f::Z3_theory_ast_callback_fptr)
    ccall((:Z3_set_new_elem_callback,"libz3"),Void,(Z3_theory,Z3_theory_ast_callback_fptr),t,f)
end

@wrap function Z3_set_init_search_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_init_search_callback,"libz3"),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

@wrap function Z3_set_push_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_push_callback,"libz3"),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

@wrap function Z3_set_pop_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_pop_callback,"libz3"),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

@wrap function Z3_set_restart_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_restart_callback,"libz3"),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

@wrap function Z3_set_reset_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_reset_callback,"libz3"),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

@wrap function Z3_set_final_check_callback(t::Z3_theory,f::Z3_theory_final_check_callback_fptr)
    ccall((:Z3_set_final_check_callback,"libz3"),Void,(Z3_theory,Z3_theory_final_check_callback_fptr),t,f)
end

@wrap function Z3_set_new_eq_callback(t::Z3_theory,f::Z3_theory_ast_ast_callback_fptr)
    ccall((:Z3_set_new_eq_callback,"libz3"),Void,(Z3_theory,Z3_theory_ast_ast_callback_fptr),t,f)
end

@wrap function Z3_set_new_diseq_callback(t::Z3_theory,f::Z3_theory_ast_ast_callback_fptr)
    ccall((:Z3_set_new_diseq_callback,"libz3"),Void,(Z3_theory,Z3_theory_ast_ast_callback_fptr),t,f)
end

@wrap function Z3_set_new_assignment_callback(t::Z3_theory,f::Z3_theory_ast_bool_callback_fptr)
    ccall((:Z3_set_new_assignment_callback,"libz3"),Void,(Z3_theory,Z3_theory_ast_bool_callback_fptr),t,f)
end

@wrap function Z3_set_new_relevant_callback(t::Z3_theory,f::Z3_theory_ast_callback_fptr)
    ccall((:Z3_set_new_relevant_callback,"libz3"),Void,(Z3_theory,Z3_theory_ast_callback_fptr),t,f)
end

@wrap function Z3_theory_assert_axiom(t::Z3_theory,ax::Z3_ast)
    ccall((:Z3_theory_assert_axiom,"libz3"),Void,(Z3_theory,Z3_ast),t,ax)
end

@wrap function Z3_theory_assume_eq(t::Z3_theory,lhs::Z3_ast,rhs::Z3_ast)
    ccall((:Z3_theory_assume_eq,"libz3"),Void,(Z3_theory,Z3_ast,Z3_ast),t,lhs,rhs)
end

@wrap function Z3_theory_enable_axiom_simplification(t::Z3_theory,flag::Z3_bool)
    ccall((:Z3_theory_enable_axiom_simplification,"libz3"),Void,(Z3_theory,Z3_bool),t,flag)
end

@wrap function Z3_theory_get_eqc_root(t::Z3_theory,n::Z3_ast)
    ccall((:Z3_theory_get_eqc_root,"libz3"),Z3_ast,(Z3_theory,Z3_ast),t,n)
end

@wrap function Z3_theory_get_eqc_next(t::Z3_theory,n::Z3_ast)
    ccall((:Z3_theory_get_eqc_next,"libz3"),Z3_ast,(Z3_theory,Z3_ast),t,n)
end

@wrap function Z3_theory_get_num_parents(t::Z3_theory,n::Z3_ast)
    ccall((:Z3_theory_get_num_parents,"libz3"),UInt32,(Z3_theory,Z3_ast),t,n)
end

@wrap function Z3_theory_get_parent(t::Z3_theory,n::Z3_ast,i::UInt32)
    ccall((:Z3_theory_get_parent,"libz3"),Z3_ast,(Z3_theory,Z3_ast,UInt32),t,n,i)
end

@wrap function Z3_theory_is_value(t::Z3_theory,n::Z3_ast)
    ccall((:Z3_theory_is_value,"libz3"),Z3_bool,(Z3_theory,Z3_ast),t,n)
end

@wrap function Z3_theory_is_decl(t::Z3_theory,d::Z3_func_decl)
    ccall((:Z3_theory_is_decl,"libz3"),Z3_bool,(Z3_theory,Z3_func_decl),t,d)
end

@wrap function Z3_theory_get_num_elems(t::Z3_theory)
    ccall((:Z3_theory_get_num_elems,"libz3"),UInt32,(Z3_theory,),t)
end

@wrap function Z3_theory_get_elem(t::Z3_theory,i::UInt32)
    ccall((:Z3_theory_get_elem,"libz3"),Z3_ast,(Z3_theory,UInt32),t,i)
end

@wrap function Z3_theory_get_num_apps(t::Z3_theory)
    ccall((:Z3_theory_get_num_apps,"libz3"),UInt32,(Z3_theory,),t)
end

@wrap function Z3_theory_get_app(t::Z3_theory,i::UInt32)
    ccall((:Z3_theory_get_app,"libz3"),Z3_ast,(Z3_theory,UInt32),t,i)
end

@wrap function Z3_mk_fixedpoint(ctx::Z3_context)
    ccall((:Z3_mk_fixedpoint,"libz3"),Z3_fixedpoint,(Z3_context,),ctx)
end

@wrap function Z3_fixedpoint_inc_ref(ctx::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_inc_ref,"libz3"),Void,(Z3_context,Z3_fixedpoint),ctx,d)
end

@wrap function Z3_fixedpoint_dec_ref(ctx::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_dec_ref,"libz3"),Void,(Z3_context,Z3_fixedpoint),ctx,d)
end

@wrap function Z3_fixedpoint_add_rule(ctx::Z3_context,d::Z3_fixedpoint,rule::Z3_ast,name::Z3_symbol)
    ccall((:Z3_fixedpoint_add_rule,"libz3"),Void,(Z3_context,Z3_fixedpoint,Z3_ast,Z3_symbol),ctx,d,rule,name)
end

@wrap function Z3_fixedpoint_add_fact(ctx::Z3_context,d::Z3_fixedpoint,r::Z3_func_decl,num_args::UInt32,args::Ref{UInt32})
    ccall((:Z3_fixedpoint_add_fact,"libz3"),Void,(Z3_context,Z3_fixedpoint,Z3_func_decl,UInt32,Ref{UInt32}),ctx,d,r,num_args,args)
end

@wrap function Z3_fixedpoint_assert(ctx::Z3_context,d::Z3_fixedpoint,axiom::Z3_ast)
    ccall((:Z3_fixedpoint_assert,"libz3"),Void,(Z3_context,Z3_fixedpoint,Z3_ast),ctx,d,axiom)
end

@wrap function Z3_fixedpoint_query(ctx::Z3_context,d::Z3_fixedpoint,query::Z3_ast)
    ccall((:Z3_fixedpoint_query,"libz3"),Z3_lbool,(Z3_context,Z3_fixedpoint,Z3_ast),ctx,d,query)
end

@wrap function Z3_fixedpoint_query_relations(ctx::Z3_context,d::Z3_fixedpoint,num_relations::UInt32,relations::Ptr{Z3_func_decl})
    ccall((:Z3_fixedpoint_query_relations,"libz3"),Z3_lbool,(Z3_context,Z3_fixedpoint,UInt32,Ptr{Z3_func_decl}),ctx,d,num_relations,relations)
end

@wrap function Z3_fixedpoint_get_answer(ctx::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_answer,"libz3"),Z3_ast,(Z3_context,Z3_fixedpoint),ctx,d)
end

@wrap function Z3_fixedpoint_get_reason_unknown(ctx::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_reason_unknown,"libz3"),Z3_string,(Z3_context,Z3_fixedpoint),ctx,d)
end

@wrap function Z3_fixedpoint_update_rule(ctx::Z3_context,d::Z3_fixedpoint,a::Z3_ast,name::Z3_symbol)
    ccall((:Z3_fixedpoint_update_rule,"libz3"),Void,(Z3_context,Z3_fixedpoint,Z3_ast,Z3_symbol),ctx,d,a,name)
end

@wrap function Z3_fixedpoint_get_num_levels(ctx::Z3_context,d::Z3_fixedpoint,pred::Z3_func_decl)
    ccall((:Z3_fixedpoint_get_num_levels,"libz3"),UInt32,(Z3_context,Z3_fixedpoint,Z3_func_decl),ctx,d,pred)
end

@wrap function Z3_fixedpoint_get_cover_delta(ctx::Z3_context,d::Z3_fixedpoint,level::Cint,pred::Z3_func_decl)
    ccall((:Z3_fixedpoint_get_cover_delta,"libz3"),Z3_ast,(Z3_context,Z3_fixedpoint,Cint,Z3_func_decl),ctx,d,level,pred)
end

@wrap function Z3_fixedpoint_add_cover(ctx::Z3_context,d::Z3_fixedpoint,level::Cint,pred::Z3_func_decl,property::Z3_ast)
    ccall((:Z3_fixedpoint_add_cover,"libz3"),Void,(Z3_context,Z3_fixedpoint,Cint,Z3_func_decl,Z3_ast),ctx,d,level,pred,property)
end

@wrap function Z3_fixedpoint_get_statistics(ctx::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_statistics,"libz3"),Z3_stats,(Z3_context,Z3_fixedpoint),ctx,d)
end

@wrap function Z3_fixedpoint_register_relation(ctx::Z3_context,d::Z3_fixedpoint,f::Z3_func_decl)
    ccall((:Z3_fixedpoint_register_relation,"libz3"),Void,(Z3_context,Z3_fixedpoint,Z3_func_decl),ctx,d,f)
end

@wrap function Z3_fixedpoint_set_predicate_representation(ctx::Z3_context,d::Z3_fixedpoint,f::Z3_func_decl,num_relations::UInt32,relation_kinds::Ptr{Z3_symbol})
    ccall((:Z3_fixedpoint_set_predicate_representation,"libz3"),Void,(Z3_context,Z3_fixedpoint,Z3_func_decl,UInt32,Ptr{Z3_symbol}),ctx,d,f,num_relations,relation_kinds)
end

@wrap function Z3_fixedpoint_get_rules(ctx::Z3_context,f::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_rules,"libz3"),Z3_ast_vector,(Z3_context,Z3_fixedpoint),ctx,f)
end

@wrap function Z3_fixedpoint_get_assertions(ctx::Z3_context,f::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_assertions,"libz3"),Z3_ast_vector,(Z3_context,Z3_fixedpoint),ctx,f)
end

@wrap function Z3_fixedpoint_set_params(ctx::Z3_context,f::Z3_fixedpoint,p::Z3_params)
    ccall((:Z3_fixedpoint_set_params,"libz3"),Void,(Z3_context,Z3_fixedpoint,Z3_params),ctx,f,p)
end

@wrap function Z3_fixedpoint_get_help(ctx::Z3_context,f::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_help,"libz3"),Z3_string,(Z3_context,Z3_fixedpoint),ctx,f)
end

@wrap function Z3_fixedpoint_get_param_descrs(ctx::Z3_context,f::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_param_descrs,"libz3"),Z3_param_descrs,(Z3_context,Z3_fixedpoint),ctx,f)
end

@wrap function Z3_fixedpoint_to_string(ctx::Z3_context,f::Z3_fixedpoint,num_queries::UInt32,queries::Ptr{Z3_ast})
    ccall((:Z3_fixedpoint_to_string,"libz3"),Z3_string,(Z3_context,Z3_fixedpoint,UInt32,Ptr{Z3_ast}),ctx,f,num_queries,queries)
end

@wrap function Z3_fixedpoint_from_string(ctx::Z3_context,f::Z3_fixedpoint,s::Z3_string)
    ccall((:Z3_fixedpoint_from_string,"libz3"),Z3_ast_vector,(Z3_context,Z3_fixedpoint,Z3_string),ctx,f,s)
end

@wrap function Z3_fixedpoint_from_file(ctx::Z3_context,f::Z3_fixedpoint,s::Z3_string)
    ccall((:Z3_fixedpoint_from_file,"libz3"),Z3_ast_vector,(Z3_context,Z3_fixedpoint,Z3_string),ctx,f,s)
end

@wrap function Z3_fixedpoint_push(ctx::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_push,"libz3"),Void,(Z3_context,Z3_fixedpoint),ctx,d)
end

@wrap function Z3_fixedpoint_pop(ctx::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_pop,"libz3"),Void,(Z3_context,Z3_fixedpoint),ctx,d)
end

@wrap function Z3_fixedpoint_init(ctx::Z3_context,d::Z3_fixedpoint,state::Ptr{Void})
    ccall((:Z3_fixedpoint_init,"libz3"),Void,(Z3_context,Z3_fixedpoint,Ptr{Void}),ctx,d,state)
end

@wrap function Z3_fixedpoint_set_reduce_assign_callback(ctx::Z3_context,d::Z3_fixedpoint,ctxb::Z3_fixedpoint_reduce_assign_callback_fptr)
    ccall((:Z3_fixedpoint_set_reduce_assign_callback,"libz3"),Void,(Z3_context,Z3_fixedpoint,Z3_fixedpoint_reduce_assign_callback_fptr),ctx,d,ctxb)
end

@wrap function Z3_fixedpoint_set_reduce_app_callback(ctx::Z3_context,d::Z3_fixedpoint,ctxb::Z3_fixedpoint_reduce_app_callback_fptr)
    ccall((:Z3_fixedpoint_set_reduce_app_callback,"libz3"),Void,(Z3_context,Z3_fixedpoint,Z3_fixedpoint_reduce_app_callback_fptr),ctx,d,ctxb)
end

@wrap function Z3_mk_ast_vector(ctx::Z3_context)
    ccall((:Z3_mk_ast_vector,"libz3"),Z3_ast_vector,(Z3_context,),ctx)
end

@wrap function Z3_ast_vector_inc_ref(ctx::Z3_context,v::Z3_ast_vector)
    ccall((:Z3_ast_vector_inc_ref,"libz3"),Void,(Z3_context,Z3_ast_vector),ctx,v)
end

@wrap function Z3_ast_vector_dec_ref(ctx::Z3_context,v::Z3_ast_vector)
    ccall((:Z3_ast_vector_dec_ref,"libz3"),Void,(Z3_context,Z3_ast_vector),ctx,v)
end

@wrap function Z3_ast_vector_size(ctx::Z3_context,v::Z3_ast_vector)
    ccall((:Z3_ast_vector_size,"libz3"),UInt32,(Z3_context,Z3_ast_vector),ctx,v)
end

@wrap function Z3_ast_vector_get(ctx::Z3_context,v::Z3_ast_vector,i::UInt32)
    ccall((:Z3_ast_vector_get,"libz3"),Z3_ast,(Z3_context,Z3_ast_vector,UInt32),ctx,v,i)
end

@wrap function Z3_ast_vector_set(ctx::Z3_context,v::Z3_ast_vector,i::UInt32,a::Z3_ast)
    ccall((:Z3_ast_vector_set,"libz3"),Void,(Z3_context,Z3_ast_vector,UInt32,Z3_ast),ctx,v,i,a)
end

@wrap function Z3_ast_vector_resize(ctx::Z3_context,v::Z3_ast_vector,n::UInt32)
    ccall((:Z3_ast_vector_resize,"libz3"),Void,(Z3_context,Z3_ast_vector,UInt32),ctx,v,n)
end

@wrap function Z3_ast_vector_push(ctx::Z3_context,v::Z3_ast_vector,a::Z3_ast)
    ccall((:Z3_ast_vector_push,"libz3"),Void,(Z3_context,Z3_ast_vector,Z3_ast),ctx,v,a)
end

@wrap function Z3_ast_vector_translate(s::Z3_context,v::Z3_ast_vector,t::Z3_context)
    ccall((:Z3_ast_vector_translate,"libz3"),Z3_ast_vector,(Z3_context,Z3_ast_vector,Z3_context),s,v,t)
end

@wrap function Z3_ast_vector_to_string(ctx::Z3_context,v::Z3_ast_vector)
    ccall((:Z3_ast_vector_to_string,"libz3"),Z3_string,(Z3_context,Z3_ast_vector),ctx,v)
end

@wrap function Z3_mk_ast_map(ctx::Z3_context)
    ccall((:Z3_mk_ast_map,"libz3"),Z3_ast_map,(Z3_context,),ctx)
end

@wrap function Z3_ast_map_inc_ref(ctx::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_inc_ref,"libz3"),Void,(Z3_context,Z3_ast_map),ctx,m)
end

@wrap function Z3_ast_map_dec_ref(ctx::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_dec_ref,"libz3"),Void,(Z3_context,Z3_ast_map),ctx,m)
end

@wrap function Z3_ast_map_contains(ctx::Z3_context,m::Z3_ast_map,k::Z3_ast)
    ccall((:Z3_ast_map_contains,"libz3"),Z3_bool,(Z3_context,Z3_ast_map,Z3_ast),ctx,m,k)
end

@wrap function Z3_ast_map_find(ctx::Z3_context,m::Z3_ast_map,k::Z3_ast)
    ccall((:Z3_ast_map_find,"libz3"),Z3_ast,(Z3_context,Z3_ast_map,Z3_ast),ctx,m,k)
end

@wrap function Z3_ast_map_insert(ctx::Z3_context,m::Z3_ast_map,k::Z3_ast,v::Z3_ast)
    ccall((:Z3_ast_map_insert,"libz3"),Void,(Z3_context,Z3_ast_map,Z3_ast,Z3_ast),ctx,m,k,v)
end

@wrap function Z3_ast_map_erase(ctx::Z3_context,m::Z3_ast_map,k::Z3_ast)
    ccall((:Z3_ast_map_erase,"libz3"),Void,(Z3_context,Z3_ast_map,Z3_ast),ctx,m,k)
end

@wrap function Z3_ast_map_reset(ctx::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_reset,"libz3"),Void,(Z3_context,Z3_ast_map),ctx,m)
end

@wrap function Z3_ast_map_size(ctx::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_size,"libz3"),UInt32,(Z3_context,Z3_ast_map),ctx,m)
end

@wrap function Z3_ast_map_keys(ctx::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_keys,"libz3"),Z3_ast_vector,(Z3_context,Z3_ast_map),ctx,m)
end

@wrap function Z3_ast_map_to_string(ctx::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_to_string,"libz3"),Z3_string,(Z3_context,Z3_ast_map),ctx,m)
end

@wrap function Z3_mk_goal(ctx::Z3_context,models::Z3_bool,unsat_cores::Z3_bool,proofs::Z3_bool)
    ccall((:Z3_mk_goal,"libz3"),Z3_goal,(Z3_context,Z3_bool,Z3_bool,Z3_bool),ctx,models,unsat_cores,proofs)
end

@wrap function Z3_goal_inc_ref(ctx::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_inc_ref,"libz3"),Void,(Z3_context,Z3_goal),ctx,g)
end

@wrap function Z3_goal_dec_ref(ctx::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_dec_ref,"libz3"),Void,(Z3_context,Z3_goal),ctx,g)
end

@wrap function Z3_goal_precision(ctx::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_precision,"libz3"),Z3_goal_prec,(Z3_context,Z3_goal),ctx,g)
end

@wrap function Z3_goal_assert(ctx::Z3_context,g::Z3_goal,a::Z3_ast)
    ccall((:Z3_goal_assert,"libz3"),Void,(Z3_context,Z3_goal,Z3_ast),ctx,g,a)
end

@wrap function Z3_goal_inconsistent(ctx::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_inconsistent,"libz3"),Z3_bool,(Z3_context,Z3_goal),ctx,g)
end

@wrap function Z3_goal_depth(ctx::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_depth,"libz3"),UInt32,(Z3_context,Z3_goal),ctx,g)
end

@wrap function Z3_goal_reset(ctx::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_reset,"libz3"),Void,(Z3_context,Z3_goal),ctx,g)
end

@wrap function Z3_goal_size(ctx::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_size,"libz3"),UInt32,(Z3_context,Z3_goal),ctx,g)
end

@wrap function Z3_goal_formula(ctx::Z3_context,g::Z3_goal,idx::UInt32)
    ccall((:Z3_goal_formula,"libz3"),Z3_ast,(Z3_context,Z3_goal,UInt32),ctx,g,idx)
end

@wrap function Z3_goal_num_exprs(ctx::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_num_exprs,"libz3"),UInt32,(Z3_context,Z3_goal),ctx,g)
end

@wrap function Z3_goal_is_decided_sat(ctx::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_is_decided_sat,"libz3"),Z3_bool,(Z3_context,Z3_goal),ctx,g)
end

@wrap function Z3_goal_is_decided_unsat(ctx::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_is_decided_unsat,"libz3"),Z3_bool,(Z3_context,Z3_goal),ctx,g)
end

@wrap function Z3_goal_translate(source::Z3_context,g::Z3_goal,target::Z3_context)
    ccall((:Z3_goal_translate,"libz3"),Z3_goal,(Z3_context,Z3_goal,Z3_context),source,g,target)
end

@wrap function Z3_goal_to_string(ctx::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_to_string,"libz3"),Z3_string,(Z3_context,Z3_goal),ctx,g)
end

@wrap function Z3_mk_tactic(ctx::Z3_context,name::Z3_string)
    ccall((:Z3_mk_tactic,"libz3"),Z3_tactic,(Z3_context,Z3_string),ctx,name)
end

@wrap function Z3_tactic_inc_ref(ctx::Z3_context,t::Z3_tactic)
    ccall((:Z3_tactic_inc_ref,"libz3"),Void,(Z3_context,Z3_tactic),ctx,t)
end

@wrap function Z3_tactic_dec_ref(ctx::Z3_context,g::Z3_tactic)
    ccall((:Z3_tactic_dec_ref,"libz3"),Void,(Z3_context,Z3_tactic),ctx,g)
end

@wrap function Z3_mk_probe(ctx::Z3_context,name::Z3_string)
    ccall((:Z3_mk_probe,"libz3"),Z3_probe,(Z3_context,Z3_string),ctx,name)
end

@wrap function Z3_probe_inc_ref(ctx::Z3_context,p::Z3_probe)
    ccall((:Z3_probe_inc_ref,"libz3"),Void,(Z3_context,Z3_probe),ctx,p)
end

@wrap function Z3_probe_dec_ref(ctx::Z3_context,p::Z3_probe)
    ccall((:Z3_probe_dec_ref,"libz3"),Void,(Z3_context,Z3_probe),ctx,p)
end

@wrap function Z3_tactic_and_then(ctx::Z3_context,t1::Z3_tactic,t2::Z3_tactic)
    ccall((:Z3_tactic_and_then,"libz3"),Z3_tactic,(Z3_context,Z3_tactic,Z3_tactic),ctx,t1,t2)
end

@wrap function Z3_tactic_or_else(ctx::Z3_context,t1::Z3_tactic,t2::Z3_tactic)
    ccall((:Z3_tactic_or_else,"libz3"),Z3_tactic,(Z3_context,Z3_tactic,Z3_tactic),ctx,t1,t2)
end

@wrap function Z3_tactic_par_or(ctx::Z3_context,num::UInt32,ts::Ptr{Z3_tactic})
    ccall((:Z3_tactic_par_or,"libz3"),Z3_tactic,(Z3_context,UInt32,Ptr{Z3_tactic}),ctx,num,ts)
end

@wrap function Z3_tactic_par_and_then(ctx::Z3_context,t1::Z3_tactic,t2::Z3_tactic)
    ccall((:Z3_tactic_par_and_then,"libz3"),Z3_tactic,(Z3_context,Z3_tactic,Z3_tactic),ctx,t1,t2)
end

@wrap function Z3_tactic_try_for(ctx::Z3_context,t::Z3_tactic,ms::UInt32)
    ccall((:Z3_tactic_try_for,"libz3"),Z3_tactic,(Z3_context,Z3_tactic,UInt32),ctx,t,ms)
end

@wrap function Z3_tactic_when(ctx::Z3_context,p::Z3_probe,t::Z3_tactic)
    ccall((:Z3_tactic_when,"libz3"),Z3_tactic,(Z3_context,Z3_probe,Z3_tactic),ctx,p,t)
end

@wrap function Z3_tactic_cond(ctx::Z3_context,p::Z3_probe,t1::Z3_tactic,t2::Z3_tactic)
    ccall((:Z3_tactic_cond,"libz3"),Z3_tactic,(Z3_context,Z3_probe,Z3_tactic,Z3_tactic),ctx,p,t1,t2)
end

@wrap function Z3_tactic_repeat(ctx::Z3_context,t::Z3_tactic,max::UInt32)
    ccall((:Z3_tactic_repeat,"libz3"),Z3_tactic,(Z3_context,Z3_tactic,UInt32),ctx,t,max)
end

@wrap function Z3_tactic_skip(ctx::Z3_context)
    ccall((:Z3_tactic_skip,"libz3"),Z3_tactic,(Z3_context,),ctx)
end

@wrap function Z3_tactic_fail(ctx::Z3_context)
    ccall((:Z3_tactic_fail,"libz3"),Z3_tactic,(Z3_context,),ctx)
end

@wrap function Z3_tactic_fail_if(ctx::Z3_context,p::Z3_probe)
    ccall((:Z3_tactic_fail_if,"libz3"),Z3_tactic,(Z3_context,Z3_probe),ctx,p)
end

@wrap function Z3_tactic_fail_if_not_decided(ctx::Z3_context)
    ccall((:Z3_tactic_fail_if_not_decided,"libz3"),Z3_tactic,(Z3_context,),ctx)
end

@wrap function Z3_tactic_using_params(ctx::Z3_context,t::Z3_tactic,p::Z3_params)
    ccall((:Z3_tactic_using_params,"libz3"),Z3_tactic,(Z3_context,Z3_tactic,Z3_params),ctx,t,p)
end

@wrap function Z3_probe_const(x::Z3_context,val::Cdouble)
    ccall((:Z3_probe_const,"libz3"),Z3_probe,(Z3_context,Cdouble),x,val)
end

@wrap function Z3_probe_lt(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_lt,"libz3"),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

@wrap function Z3_probe_gt(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_gt,"libz3"),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

@wrap function Z3_probe_le(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_le,"libz3"),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

@wrap function Z3_probe_ge(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_ge,"libz3"),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

@wrap function Z3_probe_eq(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_eq,"libz3"),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

@wrap function Z3_probe_and(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_and,"libz3"),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

@wrap function Z3_probe_or(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_or,"libz3"),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

@wrap function Z3_probe_not(x::Z3_context,p::Z3_probe)
    ccall((:Z3_probe_not,"libz3"),Z3_probe,(Z3_context,Z3_probe),x,p)
end

@wrap function Z3_get_num_tactics(ctx::Z3_context)
    ccall((:Z3_get_num_tactics,"libz3"),UInt32,(Z3_context,),ctx)
end

@wrap function Z3_get_tactic_name(ctx::Z3_context,i::UInt32)
    ccall((:Z3_get_tactic_name,"libz3"),Z3_string,(Z3_context,UInt32),ctx,i)
end

@wrap function Z3_get_num_probes(ctx::Z3_context)
    ccall((:Z3_get_num_probes,"libz3"),UInt32,(Z3_context,),ctx)
end

@wrap function Z3_get_probe_name(ctx::Z3_context,i::UInt32)
    ccall((:Z3_get_probe_name,"libz3"),Z3_string,(Z3_context,UInt32),ctx,i)
end

@wrap function Z3_tactic_get_help(ctx::Z3_context,t::Z3_tactic)
    ccall((:Z3_tactic_get_help,"libz3"),Z3_string,(Z3_context,Z3_tactic),ctx,t)
end

@wrap function Z3_tactic_get_param_descrs(ctx::Z3_context,t::Z3_tactic)
    ccall((:Z3_tactic_get_param_descrs,"libz3"),Z3_param_descrs,(Z3_context,Z3_tactic),ctx,t)
end

@wrap function Z3_tactic_get_descr(ctx::Z3_context,name::Z3_string)
    ccall((:Z3_tactic_get_descr,"libz3"),Z3_string,(Z3_context,Z3_string),ctx,name)
end

@wrap function Z3_probe_get_descr(ctx::Z3_context,name::Z3_string)
    ccall((:Z3_probe_get_descr,"libz3"),Z3_string,(Z3_context,Z3_string),ctx,name)
end

@wrap function Z3_probe_apply(ctx::Z3_context,p::Z3_probe,g::Z3_goal)
    ccall((:Z3_probe_apply,"libz3"),Cdouble,(Z3_context,Z3_probe,Z3_goal),ctx,p,g)
end

@wrap function Z3_tactic_apply(ctx::Z3_context,t::Z3_tactic,g::Z3_goal)
    ccall((:Z3_tactic_apply,"libz3"),Z3_apply_result,(Z3_context,Z3_tactic,Z3_goal),ctx,t,g)
end

@wrap function Z3_tactic_apply_ex(ctx::Z3_context,t::Z3_tactic,g::Z3_goal,p::Z3_params)
    ccall((:Z3_tactic_apply_ex,"libz3"),Z3_apply_result,(Z3_context,Z3_tactic,Z3_goal,Z3_params),ctx,t,g,p)
end

@wrap function Z3_apply_result_inc_ref(ctx::Z3_context,r::Z3_apply_result)
    ccall((:Z3_apply_result_inc_ref,"libz3"),Void,(Z3_context,Z3_apply_result),ctx,r)
end

@wrap function Z3_apply_result_dec_ref(ctx::Z3_context,r::Z3_apply_result)
    ccall((:Z3_apply_result_dec_ref,"libz3"),Void,(Z3_context,Z3_apply_result),ctx,r)
end

@wrap function Z3_apply_result_to_string(ctx::Z3_context,r::Z3_apply_result)
    ccall((:Z3_apply_result_to_string,"libz3"),Z3_string,(Z3_context,Z3_apply_result),ctx,r)
end

@wrap function Z3_apply_result_get_num_subgoals(ctx::Z3_context,r::Z3_apply_result)
    ccall((:Z3_apply_result_get_num_subgoals,"libz3"),UInt32,(Z3_context,Z3_apply_result),ctx,r)
end

@wrap function Z3_apply_result_get_subgoal(ctx::Z3_context,r::Z3_apply_result,i::UInt32)
    ccall((:Z3_apply_result_get_subgoal,"libz3"),Z3_goal,(Z3_context,Z3_apply_result,UInt32),ctx,r,i)
end

@wrap function Z3_apply_result_convert_model(ctx::Z3_context,r::Z3_apply_result,i::UInt32,m::Z3_model)
    ccall((:Z3_apply_result_convert_model,"libz3"),Z3_model,(Z3_context,Z3_apply_result,UInt32,Z3_model),ctx,r,i,m)
end

@wrap function Z3_mk_solver(ctx::Z3_context)
    ccall((:Z3_mk_solver,"libz3"),Z3_solver,(Z3_context,),ctx)
end

@wrap function Z3_mk_simple_solver(ctx::Z3_context)
    ccall((:Z3_mk_simple_solver,"libz3"),Z3_solver,(Z3_context,),ctx)
end

@wrap function Z3_mk_solver_for_logic(ctx::Z3_context,logic::Z3_symbol)
    ccall((:Z3_mk_solver_for_logic,"libz3"),Z3_solver,(Z3_context,Z3_symbol),ctx,logic)
end

@wrap function Z3_mk_solver_from_tactic(ctx::Z3_context,t::Z3_tactic)
    ccall((:Z3_mk_solver_from_tactic,"libz3"),Z3_solver,(Z3_context,Z3_tactic),ctx,t)
end

@wrap function Z3_solver_get_help(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_help,"libz3"),Z3_string,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_get_param_descrs(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_param_descrs,"libz3"),Z3_param_descrs,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_set_params(ctx::Z3_context,s::Z3_solver,p::Z3_params)
    ccall((:Z3_solver_set_params,"libz3"),Void,(Z3_context,Z3_solver,Z3_params),ctx,s,p)
end

@wrap function Z3_solver_inc_ref(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_inc_ref,"libz3"),Void,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_dec_ref(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_dec_ref,"libz3"),Void,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_push(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_push,"libz3"),Void,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_pop(ctx::Z3_context,s::Z3_solver,n::UInt32)
    ccall((:Z3_solver_pop,"libz3"),Void,(Z3_context,Z3_solver,UInt32),ctx,s,n)
end

@wrap function Z3_solver_reset(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_reset,"libz3"),Void,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_get_num_scopes(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_num_scopes,"libz3"),UInt32,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_assert(ctx::Z3_context,s::Z3_solver,a::Z3_ast)
    ccall((:Z3_solver_assert,"libz3"),Void,(Z3_context,Z3_solver,Z3_ast),ctx,s,a)
end

@wrap function Z3_solver_assert_and_track(ctx::Z3_context,s::Z3_solver,a::Z3_ast,p::Z3_ast)
    ccall((:Z3_solver_assert_and_track,"libz3"),Void,(Z3_context,Z3_solver,Z3_ast,Z3_ast),ctx,s,a,p)
end

@wrap function Z3_solver_get_assertions(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_assertions,"libz3"),Z3_ast_vector,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_check(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_check,"libz3"),Z3_lbool,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_check_assumptions(ctx::Z3_context,s::Z3_solver,num_assumptions::UInt32,assumptions::Ptr{Z3_ast})
    ccall((:Z3_solver_check_assumptions,"libz3"),Z3_lbool,(Z3_context,Z3_solver,UInt32,Ptr{Z3_ast}),ctx,s,num_assumptions,assumptions)
end

@wrap function Z3_solver_get_model(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_model,"libz3"),Z3_model,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_get_proof(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_proof,"libz3"),Z3_ast,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_get_unsat_core(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_unsat_core,"libz3"),Z3_ast_vector,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_get_reason_unknown(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_reason_unknown,"libz3"),Z3_string,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_get_statistics(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_statistics,"libz3"),Z3_stats,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_solver_to_string(ctx::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_to_string,"libz3"),Z3_string,(Z3_context,Z3_solver),ctx,s)
end

@wrap function Z3_stats_to_string(ctx::Z3_context,s::Z3_stats)
    ccall((:Z3_stats_to_string,"libz3"),Z3_string,(Z3_context,Z3_stats),ctx,s)
end

@wrap function Z3_stats_inc_ref(ctx::Z3_context,s::Z3_stats)
    ccall((:Z3_stats_inc_ref,"libz3"),Void,(Z3_context,Z3_stats),ctx,s)
end

@wrap function Z3_stats_dec_ref(ctx::Z3_context,s::Z3_stats)
    ccall((:Z3_stats_dec_ref,"libz3"),Void,(Z3_context,Z3_stats),ctx,s)
end

@wrap function Z3_stats_size(ctx::Z3_context,s::Z3_stats)
    ccall((:Z3_stats_size,"libz3"),UInt32,(Z3_context,Z3_stats),ctx,s)
end

@wrap function Z3_stats_get_key(ctx::Z3_context,s::Z3_stats,idx::UInt32)
    ccall((:Z3_stats_get_key,"libz3"),Z3_string,(Z3_context,Z3_stats,UInt32),ctx,s,idx)
end

@wrap function Z3_stats_is_uint(ctx::Z3_context,s::Z3_stats,idx::UInt32)
    ccall((:Z3_stats_is_uint,"libz3"),Z3_bool,(Z3_context,Z3_stats,UInt32),ctx,s,idx)
end

@wrap function Z3_stats_is_double(ctx::Z3_context,s::Z3_stats,idx::UInt32)
    ccall((:Z3_stats_is_double,"libz3"),Z3_bool,(Z3_context,Z3_stats,UInt32),ctx,s,idx)
end

@wrap function Z3_stats_get_uint_value(ctx::Z3_context,s::Z3_stats,idx::UInt32)
    ccall((:Z3_stats_get_uint_value,"libz3"),UInt32,(Z3_context,Z3_stats,UInt32),ctx,s,idx)
end

@wrap function Z3_stats_get_double_value(ctx::Z3_context,s::Z3_stats,idx::UInt32)
    ccall((:Z3_stats_get_double_value,"libz3"),Cdouble,(Z3_context,Z3_stats,UInt32),ctx,s,idx)
end

@wrap function Z3_mk_injective_function(ctx::Z3_context,s::Z3_symbol,domain_size::UInt32,domain::Ptr{Z3_sort},range::Z3_sort)
    ccall((:Z3_mk_injective_function,"libz3"),Z3_func_decl,(Z3_context,Z3_symbol,UInt32,Ptr{Z3_sort},Z3_sort),ctx,s,domain_size,domain,range)
end

@wrap function Z3_set_logic(ctx::Z3_context,logic::Z3_string)
    ccall((:Z3_set_logic,"libz3"),Z3_bool,(Z3_context,Z3_string),ctx,logic)
end

@wrap function Z3_push(ctx::Z3_context)
    ccall((:Z3_push,"libz3"),Void,(Z3_context,),ctx)
end

@wrap function Z3_pop(ctx::Z3_context,num_scopes::UInt32)
    ccall((:Z3_pop,"libz3"),Void,(Z3_context,UInt32),ctx,num_scopes)
end

@wrap function Z3_get_num_scopes(ctx::Z3_context)
    ccall((:Z3_get_num_scopes,"libz3"),UInt32,(Z3_context,),ctx)
end

@wrap function Z3_persist_ast(ctx::Z3_context,a::Z3_ast,num_scopes::UInt32)
    ccall((:Z3_persist_ast,"libz3"),Void,(Z3_context,Z3_ast,UInt32),ctx,a,num_scopes)
end

@wrap function Z3_assert_cnstr(ctx::Z3_context,a::Z3_ast)
    ccall((:Z3_assert_cnstr,"libz3"),Void,(Z3_context,Z3_ast),ctx,a)
end

@wrap function Z3_check_and_get_model(ctx::Z3_context,m::Ptr{Z3_model})
    ccall((:Z3_check_and_get_model,"libz3"),Z3_lbool,(Z3_context,Ptr{Z3_model}),ctx,m)
end

# Deprecated
# @wrap function Z3_check(ctx::Z3_context)
#     ccall((:Z3_check,"libz3"),Z3_lbool,(Z3_context,),ctx)
# end

@wrap function Z3_check_assumptions(ctx::Z3_context,num_assumptions::UInt32,assumptions::Ptr{Z3_ast},m::Ptr{Z3_model},proof::Ptr{Z3_ast},ctxore_size::Ref{UInt32},ctxore::Ptr{Z3_ast})
    ccall((:Z3_check_assumptions,"libz3"),Z3_lbool,(Z3_context,UInt32,Ptr{Z3_ast},Ptr{Z3_model},Ptr{Z3_ast},Ref{UInt32},Ptr{Z3_ast}),ctx,num_assumptions,assumptions,m,proof,ctxore_size,ctxore)
end

@wrap function Z3_get_implied_equalities(ctx::Z3_context,s::Z3_solver,num_terms::UInt32,terms::Ptr{Z3_ast},ctxlass_ids::Ref{UInt32})
    ccall((:Z3_get_implied_equalities,"libz3"),Z3_lbool,(Z3_context,Z3_solver,UInt32,Ptr{Z3_ast},Ref{UInt32}),ctx,s,num_terms,terms,ctxlass_ids)
end

@wrap function Z3_del_model(ctx::Z3_context,m::Z3_model)
    ccall((:Z3_del_model,"libz3"),Void,(Z3_context,Z3_model),ctx,m)
end

@wrap function Z3_soft_check_cancel(ctx::Z3_context)
    ccall((:Z3_soft_check_cancel,"libz3"),Void,(Z3_context,),ctx)
end

@wrap function Z3_get_search_failure(ctx::Z3_context)
    ccall((:Z3_get_search_failure,"libz3"),Z3_search_failure,(Z3_context,),ctx)
end

@wrap function Z3_mk_label(ctx::Z3_context,s::Z3_symbol,is_pos::Z3_bool,f::Z3_ast)
    ccall((:Z3_mk_label,"libz3"),Z3_ast,(Z3_context,Z3_symbol,Z3_bool,Z3_ast),ctx,s,is_pos,f)
end

@wrap function Z3_get_relevant_labels(ctx::Z3_context)
    ccall((:Z3_get_relevant_labels,"libz3"),Z3_literals,(Z3_context,),ctx)
end

@wrap function Z3_get_relevant_literals(ctx::Z3_context)
    ccall((:Z3_get_relevant_literals,"libz3"),Z3_literals,(Z3_context,),ctx)
end

@wrap function Z3_get_guessed_literals(ctx::Z3_context)
    ccall((:Z3_get_guessed_literals,"libz3"),Z3_literals,(Z3_context,),ctx)
end

@wrap function Z3_del_literals(ctx::Z3_context,lbls::Z3_literals)
    ccall((:Z3_del_literals,"libz3"),Void,(Z3_context,Z3_literals),ctx,lbls)
end

@wrap function Z3_get_num_literals(ctx::Z3_context,lbls::Z3_literals)
    ccall((:Z3_get_num_literals,"libz3"),UInt32,(Z3_context,Z3_literals),ctx,lbls)
end

@wrap function Z3_get_label_symbol(ctx::Z3_context,lbls::Z3_literals,idx::UInt32)
    ccall((:Z3_get_label_symbol,"libz3"),Z3_symbol,(Z3_context,Z3_literals,UInt32),ctx,lbls,idx)
end

@wrap function Z3_get_literal(ctx::Z3_context,lbls::Z3_literals,idx::UInt32)
    ccall((:Z3_get_literal,"libz3"),Z3_ast,(Z3_context,Z3_literals,UInt32),ctx,lbls,idx)
end

@wrap function Z3_disable_literal(ctx::Z3_context,lbls::Z3_literals,idx::UInt32)
    ccall((:Z3_disable_literal,"libz3"),Void,(Z3_context,Z3_literals,UInt32),ctx,lbls,idx)
end

@wrap function Z3_block_literals(ctx::Z3_context,lbls::Z3_literals)
    ccall((:Z3_block_literals,"libz3"),Void,(Z3_context,Z3_literals),ctx,lbls)
end

@wrap function Z3_get_model_num_constants(ctx::Z3_context,m::Z3_model)
    ccall((:Z3_get_model_num_constants,"libz3"),UInt32,(Z3_context,Z3_model),ctx,m)
end

@wrap function Z3_get_model_constant(ctx::Z3_context,m::Z3_model,i::UInt32)
    ccall((:Z3_get_model_constant,"libz3"),Z3_func_decl,(Z3_context,Z3_model,UInt32),ctx,m,i)
end

@wrap function Z3_get_model_num_funcs(ctx::Z3_context,m::Z3_model)
    ccall((:Z3_get_model_num_funcs,"libz3"),UInt32,(Z3_context,Z3_model),ctx,m)
end

@wrap function Z3_get_model_func_decl(ctx::Z3_context,m::Z3_model,i::UInt32)
    ccall((:Z3_get_model_func_decl,"libz3"),Z3_func_decl,(Z3_context,Z3_model,UInt32),ctx,m,i)
end

@wrap function Z3_eval_func_decl(ctx::Z3_context,m::Z3_model,decl::Z3_func_decl,v::Ptr{Z3_ast})
    ccall((:Z3_eval_func_decl,"libz3"),Z3_bool,(Z3_context,Z3_model,Z3_func_decl,Ptr{Z3_ast}),ctx,m,decl,v)
end

@wrap function Z3_is_array_value(ctx::Z3_context,m::Z3_model,v::Z3_ast,num_entries::Ref{UInt32})
    ccall((:Z3_is_array_value,"libz3"),Z3_bool,(Z3_context,Z3_model,Z3_ast,Ref{UInt32}),ctx,m,v,num_entries)
end

@wrap function Z3_get_array_value(ctx::Z3_context,m::Z3_model,v::Z3_ast,num_entries::UInt32,indices::Ptr{Z3_ast},values::Ptr{Z3_ast},else_value::Ptr{Z3_ast})
    ccall((:Z3_get_array_value,"libz3"),Void,(Z3_context,Z3_model,Z3_ast,UInt32,Ptr{Z3_ast},Ptr{Z3_ast},Ptr{Z3_ast}),ctx,m,v,num_entries,indices,values,else_value)
end

@wrap function Z3_get_model_func_else(ctx::Z3_context,m::Z3_model,i::UInt32)
    ccall((:Z3_get_model_func_else,"libz3"),Z3_ast,(Z3_context,Z3_model,UInt32),ctx,m,i)
end

@wrap function Z3_get_model_func_num_entries(ctx::Z3_context,m::Z3_model,i::UInt32)
    ccall((:Z3_get_model_func_num_entries,"libz3"),UInt32,(Z3_context,Z3_model,UInt32),ctx,m,i)
end

@wrap function Z3_get_model_func_entry_num_args(ctx::Z3_context,m::Z3_model,i::UInt32,j::UInt32)
    ccall((:Z3_get_model_func_entry_num_args,"libz3"),UInt32,(Z3_context,Z3_model,UInt32,UInt32),ctx,m,i,j)
end

@wrap function Z3_get_model_func_entry_arg(ctx::Z3_context,m::Z3_model,i::UInt32,j::UInt32,k::UInt32)
    ccall((:Z3_get_model_func_entry_arg,"libz3"),Z3_ast,(Z3_context,Z3_model,UInt32,UInt32,UInt32),ctx,m,i,j,k)
end

@wrap function Z3_get_model_func_entry_value(ctx::Z3_context,m::Z3_model,i::UInt32,j::UInt32)
    ccall((:Z3_get_model_func_entry_value,"libz3"),Z3_ast,(Z3_context,Z3_model,UInt32,UInt32),ctx,m,i,j)
end

#Fix me macro is making this eval so its clashing with Julia eval, have a better way to parse
@wrap function Z3_z3eval(ctx::Z3_context,m::Z3_model,t::Z3_ast,v::Ptr{Z3_ast})
    ccall((:Z3_eval,"libz3"),Z3_bool,(Z3_context,Z3_model,Z3_ast,Ptr{Z3_ast}),ctx,m,t,v)
end

@wrap function Z3_eval_decl(ctx::Z3_context,m::Z3_model,d::Z3_func_decl,num_args::UInt32,args::Ptr{Z3_ast},v::Ptr{Z3_ast})
    ccall((:Z3_eval_decl,"libz3"),Z3_bool,(Z3_context,Z3_model,Z3_func_decl,UInt32,Ptr{Z3_ast},Ptr{Z3_ast}),ctx,m,d,num_args,args,v)
end

@wrap function Z3_context_to_string(ctx::Z3_context)
    ccall((:Z3_context_to_string,"libz3"),Z3_string,(Z3_context,),ctx)
end

@wrap function Z3_statistics_to_string(ctx::Z3_context)
    ccall((:Z3_statistics_to_string,"libz3"),Z3_string,(Z3_context,),ctx)
end

@wrap function Z3_get_context_assignment(ctx::Z3_context)
    ccall((:Z3_get_context_assignment,"libz3"),Z3_ast,(Z3_context,),ctx)
end
