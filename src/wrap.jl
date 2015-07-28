#ifdef CorML3
typealias Z3_symbol Ptr{Void}
typealias Z3_literals Ptr{Void}
typealias Z3_theory Ptr{Void}
typealias Z3_config Ptr{Void}
typealias Z3_context Ptr{Void}
typealias Z3_sort Ptr{Void}
#define Z3_sort_opt Z3_sort
typealias Z3_func_decl Ptr{Void}
typealias Z3_ast Ptr{Void}
#define Z3_ast_opt Z3_ast
typealias Z3_app Ptr{Void}
typealias Z3_pattern Ptr{Void}
typealias Z3_model Ptr{Void}
typealias Z3_constructor Ptr{Void}
typealias Z3_constructor_list Ptr{Void}
#endif
#ifdef Conly
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
#define Z3_func_interp_opt Z3_func_interp
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

typealias Z3_error_handler Ptr{Void}

typealias Z3_fixedpoint_reduce_assign_callback_fptr Ptr{Void}
typealias Z3_fixedpoint_reduce_app_callback_fptr Ptr{Void}

typealias Z3_string Ptr{Uint8}
typealias Z3_string_ptr Ptr{Ptr{Uint8}}
typealias Z3_bool Cint

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
typealias Z3BoolPtr Ptr{Void}
typealias FixedpointReduceAssignCallbackFptrPtr Ptr{Void}
typealias FixedpointReduceAppCallbackFptrPtr Ptr{Void}

#ifdef CorML3

abstract Z3CType
convert(::Type{Ptr{Void}}, x::Z3CType) = x.ptr
convert(::Type{Z3_string}, x::ASCIIString) = pointer(x)

type Z3Symbol <: Z3CType ptr::Z3SymbolPtr end
type Literals <: Z3CType ptr::LiteralsPtr end
type Theory <: Z3CType ptr::TheoryPtr end
type Config <: Z3CType ptr::ConfigPtr end
type Context <: Z3CType ptr::ContextPtr end
type Sort <: Z3CType ptr::SortPtr end
#define Z3SortOpt Z3Sort
type FuncDecl <: Z3CType ptr::FuncDeclPtr end
type Ast <: Z3CType ptr::AstPtr end
#define Z3AstOpt Z3Ast
type App <: Z3CType ptr::AppPtr end
type Pattern <: Z3CType ptr::PatternPtr end
type Model <: Z3CType ptr::ModelPtr end
type Constructor <: Z3CType ptr::ConstructorPtr end
type ConstructorList <: Z3CType ptr::ConstructorListPtr end
#endif
#ifdef Conly
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
#define Z3FuncInterpOpt Z3FuncInterp
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

type Z3Bool <: Z3CType ptr::Z3BoolPtr end

type FixedpointReduceAssignCallbackFptr <: Z3CType ptr::FixedpointReduceAssignCallbackFptrPtr end
type FixedpointReduceAppCallbackFptr <: Z3CType ptr::FixedpointReduceAppCallbackFptrPtr end

## Enums
## =====
"Lifted Boolean type: \c false, \c undefined, \c true."
@enum Z3_lbool Z3_L_FALSE = -1 Z3_L_UNDEF Z3_L_TRUE

"""The different kinds of symbol.
In Z3, a symbol can be represented using integers and strings"""
@enum Z3_symbol_kind Z3_INT_SYMBOL Z3_STRING_SYMBOL

@enum Z3_parameter_kind Z3_PARAMETER_INT Z3_PARAMETER_DOUBLE Z3_PARAMETER_RATIONAL Z3_PARAMETER_SYMBOL Z3_PARAMETER_SORT Z3_PARAMETER_AST Z3_PARAMETER_FUNC_DECL

"The different kinds of Z3 types"
@enum Z3_sort_kind Z3_UNINTERPRETED_SORT Z3_BOOL_SORT Z3_INT_SORT Z3_REAL_SORT Z3_BV_SORT Z3_ARRAY_SORT Z3_DATATYPE_SORT Z3_RELATION_SORT Z3_FINITE_DOMAIN_SORT Z3_UNKNOWN_SORT = 1000

"The different kinds of Z3 AST (abstract syntax trees). That is, terms, formulas and types."
@enum Z3_ast_kind Z3_NUMERAL_AST Z3_APP_AST Z3_VAR_AST Z3_QUANTIFIER_AST Z3_SORT_AST Z3_FUNC_DECL_AST Z3_UNKNOWN_AST = 1000

"The different kinds of interpreted function kinds."
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

"The different kinds of parameters that can be associated with parameter sets."
@enum(Z3_param_kind,
      Z3_PK_UINT,
      Z3_PK_BOOL,
      Z3_PK_DOUBLE,
      Z3_PK_SYMBOL,
      Z3_PK_STRING,
      Z3_PK_OTHER,
      Z3_PK_INVALID)

"The different kinds of search failure types."
@enum(Z3_search_failure,
      Z3_NO_FAILURE,
      Z3_UNKNOWN,
      Z3_TIMEOUT,
      Z3_MEMOUT_WATERMARK,
      Z3_CANCELED,
      Z3_NUM_CONFLICTS,
      Z3_THEORY,
      Z3_QUANTIFIERS)

"Z3 pretty printing modes (See #Z3_set_ast_print_mode)."
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

## functions
## =========
z3tojulia = Dict(:Z3_symbol => :Z3Symbol,
            :Z3_literals => :Literals,
            :Z3_theory => :Theory,
            :Z3_config => :Config,
            :Z3_context => :Context,
            :Z3_sort => :Sort,
            :Z3_func_decl => :FuncDecl,
            :Z3_ast => :Ast,
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
function convert_typ(typ::Symbol)
  if typ == :(Z3_string)
    :ASCIIString
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
  # # ASCIISTring
  # if typ == :(Z3_string)
  #   :(pointer($name))
  # elseif typ == :(Uint32)
  #   name
  # elseif typ == :(Cdouble)
  #   name
  # else
  #   warning("Arg of type $arg not handled")
  # end
end

"""For a z3 ccall wrapper function (below), `wrap` creates an additional function
which accepts the Julia wrapper types and does necessary conversions"""
macro wrap(func_def)
  # FIXME: finding return_type in this way is very brittle
  println()
  @show return_type = func_def.args[2].args[2].args[2]
  @show name = func_def.args[1].args[1]
  @show short_name = symbol(string(name)[4:end])
  @show func_args = func_def.args[1].args[2:end]

  new_return_typ = convert_typ(return_type)

  @show params = Expr(:call, short_name, [convert_arg(arg) for arg in func_args]...)
  @show api_call = Expr(:call, name, [handle_call(arg) for arg in func_args]...)
  @show wrapped_call = Expr(:call, :convert, new_return_typ, api_call)
  @show func_decl = Expr(:function, params, wrapped_call)
  @show :(begin
            $func_def
            $func_decl
          end)
end

## functions
## =========


function Z3_global_param_set(param_id::Z3_string,param_value::Z3_string)
    ccall((:Z3_global_param_set,testclang),Void,(Z3_string,Z3_string),param_id,param_value)
end

function Z3_global_param_reset_all()
    ccall((:Z3_global_param_reset_all,testclang),Void,())
end

function Z3_global_param_get(param_id::Z3_string,param_value::Z3_string_ptr)
    ccall((:Z3_global_param_get,testclang),Z3_bool,(Z3_string,Z3_string_ptr),param_id,param_value)
end

function Z3_mk_config()
    ccall((:Z3_mk_config,testclang),Z3_config,())
end

function Z3_del_config(c::Z3_config)
    ccall((:Z3_del_config,testclang),Void,(Z3_config,),c)
end

function Z3_set_param_value(c::Z3_config,param_id::Z3_string,param_value::Z3_string)
    ccall((:Z3_set_param_value,testclang),Void,(Z3_config,Z3_string,Z3_string),c,param_id,param_value)
end

@wrap function Z3_mk_context(c::Z3_config)
    ccall((:Z3_mk_context,testclang),Z3_context,(Z3_config,),c)
end

function Z3_mk_context_rc(c::Z3_config)
    ccall((:Z3_mk_context_rc,testclang),Z3_context,(Z3_config,),c)
end

function Z3_del_context(c::Z3_context)
    ccall((:Z3_del_context,testclang),Void,(Z3_context,),c)
end

function Z3_inc_ref(c::Z3_context,a::Z3_ast)
    ccall((:Z3_inc_ref,testclang),Void,(Z3_context,Z3_ast),c,a)
end

function Z3_dec_ref(c::Z3_context,a::Z3_ast)
    ccall((:Z3_dec_ref,testclang),Void,(Z3_context,Z3_ast),c,a)
end

function Z3_update_param_value(c::Z3_context,param_id::Z3_string,param_value::Z3_string)
    ccall((:Z3_update_param_value,testclang),Void,(Z3_context,Z3_string,Z3_string),c,param_id,param_value)
end

function Z3_interrupt(c::Z3_context)
    ccall((:Z3_interrupt,testclang),Void,(Z3_context,),c)
end

function Z3_mk_params(c::Z3_context)
    ccall((:Z3_mk_params,testclang),Z3_params,(Z3_context,),c)
end

function Z3_params_inc_ref(c::Z3_context,p::Z3_params)
    ccall((:Z3_params_inc_ref,testclang),Void,(Z3_context,Z3_params),c,p)
end

function Z3_params_dec_ref(c::Z3_context,p::Z3_params)
    ccall((:Z3_params_dec_ref,testclang),Void,(Z3_context,Z3_params),c,p)
end

function Z3_params_set_bool(c::Z3_context,p::Z3_params,k::Z3_symbol,v::Z3_bool)
    ccall((:Z3_params_set_bool,testclang),Void,(Z3_context,Z3_params,Z3_symbol,Z3_bool),c,p,k,v)
end

function Z3_params_set_uint(c::Z3_context,p::Z3_params,k::Z3_symbol,v::Uint32)
    ccall((:Z3_params_set_uint,testclang),Void,(Z3_context,Z3_params,Z3_symbol,Uint32),c,p,k,v)
end

function Z3_params_set_double(c::Z3_context,p::Z3_params,k::Z3_symbol,v::Cdouble)
    ccall((:Z3_params_set_double,testclang),Void,(Z3_context,Z3_params,Z3_symbol,Cdouble),c,p,k,v)
end

function Z3_params_set_symbol(c::Z3_context,p::Z3_params,k::Z3_symbol,v::Z3_symbol)
    ccall((:Z3_params_set_symbol,testclang),Void,(Z3_context,Z3_params,Z3_symbol,Z3_symbol),c,p,k,v)
end

function Z3_params_to_string(c::Z3_context,p::Z3_params)
    ccall((:Z3_params_to_string,testclang),Z3_string,(Z3_context,Z3_params),c,p)
end

function Z3_params_validate(c::Z3_context,p::Z3_params,d::Z3_param_descrs)
    ccall((:Z3_params_validate,testclang),Void,(Z3_context,Z3_params,Z3_param_descrs),c,p,d)
end

function Z3_param_descrs_inc_ref(c::Z3_context,p::Z3_param_descrs)
    ccall((:Z3_param_descrs_inc_ref,testclang),Void,(Z3_context,Z3_param_descrs),c,p)
end

function Z3_param_descrs_dec_ref(c::Z3_context,p::Z3_param_descrs)
    ccall((:Z3_param_descrs_dec_ref,testclang),Void,(Z3_context,Z3_param_descrs),c,p)
end

function Z3_param_descrs_get_kind(c::Z3_context,p::Z3_param_descrs,n::Z3_symbol)
    ccall((:Z3_param_descrs_get_kind,testclang),Z3_param_kind,(Z3_context,Z3_param_descrs,Z3_symbol),c,p,n)
end

function Z3_param_descrs_size(c::Z3_context,p::Z3_param_descrs)
    ccall((:Z3_param_descrs_size,testclang),Uint32,(Z3_context,Z3_param_descrs),c,p)
end

function Z3_param_descrs_get_name(c::Z3_context,p::Z3_param_descrs,i::Uint32)
    ccall((:Z3_param_descrs_get_name,testclang),Z3_symbol,(Z3_context,Z3_param_descrs,Uint32),c,p,i)
end

function Z3_param_descrs_to_string(c::Z3_context,p::Z3_param_descrs)
    ccall((:Z3_param_descrs_to_string,testclang),Z3_string,(Z3_context,Z3_param_descrs),c,p)
end

function Z3_mk_int_symbol(c::Z3_context,i::Cint)
    ccall((:Z3_mk_int_symbol,testclang),Z3_symbol,(Z3_context,Cint),c,i)
end

function Z3_mk_string_symbol(c::Z3_context,s::Z3_string)
    ccall((:Z3_mk_string_symbol,testclang),Z3_symbol,(Z3_context,Z3_string),c,s)
end

function Z3_mk_uninterpreted_sort(c::Z3_context,s::Z3_symbol)
    ccall((:Z3_mk_uninterpreted_sort,testclang),Z3_sort,(Z3_context,Z3_symbol),c,s)
end

function Z3_mk_bool_sort(c::Z3_context)
    ccall((:Z3_mk_bool_sort,testclang),Z3_sort,(Z3_context,),c)
end

function Z3_mk_int_sort(c::Z3_context)
    ccall((:Z3_mk_int_sort,testclang),Z3_sort,(Z3_context,),c)
end

function Z3_mk_real_sort(c::Z3_context)
    ccall((:Z3_mk_real_sort,testclang),Z3_sort,(Z3_context,),c)
end

function Z3_mk_bv_sort(c::Z3_context,sz::Uint32)
    ccall((:Z3_mk_bv_sort,testclang),Z3_sort,(Z3_context,Uint32),c,sz)
end

function Z3_mk_finite_domain_sort(c::Z3_context,name::Z3_symbol,size::Culonglong)
    ccall((:Z3_mk_finite_domain_sort,testclang),Z3_sort,(Z3_context,Z3_symbol,Culonglong),c,name,size)
end

function Z3_mk_array_sort(c::Z3_context,domain::Z3_sort,range::Z3_sort)
    ccall((:Z3_mk_array_sort,testclang),Z3_sort,(Z3_context,Z3_sort,Z3_sort),c,domain,range)
end

function Z3_mk_tuple_sort(c::Z3_context,mk_tuple_name::Z3_symbol,num_fields::Uint32,field_names::Ptr{Z3_symbol},field_sorts::Ptr{Z3_sort},mk_tuple_decl::Ptr{Z3_func_decl},proj_decl::Ptr{Z3_func_decl})
    ccall((:Z3_mk_tuple_sort,testclang),Z3_sort,(Z3_context,Z3_symbol,Uint32,Ptr{Z3_symbol},Ptr{Z3_sort},Ptr{Z3_func_decl},Ptr{Z3_func_decl}),c,mk_tuple_name,num_fields,field_names,field_sorts,mk_tuple_decl,proj_decl)
end

function Z3_mk_enumeration_sort(c::Z3_context,name::Z3_symbol,n::Uint32,enum_names::Ptr{Z3_symbol},enum_consts::Ptr{Z3_func_decl},enum_testers::Ptr{Z3_func_decl})
    ccall((:Z3_mk_enumeration_sort,testclang),Z3_sort,(Z3_context,Z3_symbol,Uint32,Ptr{Z3_symbol},Ptr{Z3_func_decl},Ptr{Z3_func_decl}),c,name,n,enum_names,enum_consts,enum_testers)
end

function Z3_mk_list_sort(c::Z3_context,name::Z3_symbol,elem_sort::Z3_sort,nil_decl::Ptr{Z3_func_decl},is_nil_decl::Ptr{Z3_func_decl},cons_decl::Ptr{Z3_func_decl},is_cons_decl::Ptr{Z3_func_decl},head_decl::Ptr{Z3_func_decl},tail_decl::Ptr{Z3_func_decl})
    ccall((:Z3_mk_list_sort,testclang),Z3_sort,(Z3_context,Z3_symbol,Z3_sort,Ptr{Z3_func_decl},Ptr{Z3_func_decl},Ptr{Z3_func_decl},Ptr{Z3_func_decl},Ptr{Z3_func_decl},Ptr{Z3_func_decl}),c,name,elem_sort,nil_decl,is_nil_decl,cons_decl,is_cons_decl,head_decl,tail_decl)
end

function Z3_mk_constructor(c::Z3_context,name::Z3_symbol,recognizer::Z3_symbol,num_fields::Uint32,field_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},sort_refs::Ptr{Uint32})
    ccall((:Z3_mk_constructor,testclang),Z3_constructor,(Z3_context,Z3_symbol,Z3_symbol,Uint32,Ptr{Z3_symbol},Ptr{Z3_sort},Ptr{Uint32}),c,name,recognizer,num_fields,field_names,sorts,sort_refs)
end

function Z3_del_constructor(c::Z3_context,constr::Z3_constructor)
    ccall((:Z3_del_constructor,testclang),Void,(Z3_context,Z3_constructor),c,constr)
end

function Z3_mk_datatype(c::Z3_context,name::Z3_symbol,num_constructors::Uint32,constructors::Ptr{Z3_constructor})
    ccall((:Z3_mk_datatype,testclang),Z3_sort,(Z3_context,Z3_symbol,Uint32,Ptr{Z3_constructor}),c,name,num_constructors,constructors)
end

function Z3_mk_constructor_list(c::Z3_context,num_constructors::Uint32,constructors::Ptr{Z3_constructor})
    ccall((:Z3_mk_constructor_list,testclang),Z3_constructor_list,(Z3_context,Uint32,Ptr{Z3_constructor}),c,num_constructors,constructors)
end

function Z3_del_constructor_list(c::Z3_context,clist::Z3_constructor_list)
    ccall((:Z3_del_constructor_list,testclang),Void,(Z3_context,Z3_constructor_list),c,clist)
end

function Z3_mk_datatypes(c::Z3_context,num_sorts::Uint32,sort_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},constructor_lists::Ptr{Z3_constructor_list})
    ccall((:Z3_mk_datatypes,testclang),Void,(Z3_context,Uint32,Ptr{Z3_symbol},Ptr{Z3_sort},Ptr{Z3_constructor_list}),c,num_sorts,sort_names,sorts,constructor_lists)
end

function Z3_query_constructor(c::Z3_context,constr::Z3_constructor,num_fields::Uint32,constructor::Ptr{Z3_func_decl},tester::Ptr{Z3_func_decl},accessors::Ptr{Z3_func_decl})
    ccall((:Z3_query_constructor,testclang),Void,(Z3_context,Z3_constructor,Uint32,Ptr{Z3_func_decl},Ptr{Z3_func_decl},Ptr{Z3_func_decl}),c,constr,num_fields,constructor,tester,accessors)
end

function Z3_mk_func_decl(c::Z3_context,s::Z3_symbol,domain_size::Uint32,domain::Ptr{Z3_sort},range::Z3_sort)
    ccall((:Z3_mk_func_decl,testclang),Z3_func_decl,(Z3_context,Z3_symbol,Uint32,Ptr{Z3_sort},Z3_sort),c,s,domain_size,domain,range)
end

function Z3_mk_app(c::Z3_context,d::Z3_func_decl,num_args::Uint32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_app,testclang),Z3_ast,(Z3_context,Z3_func_decl,Uint32,Ptr{Z3_ast}),c,d,num_args,args)
end

function Z3_mk_const(c::Z3_context,s::Z3_symbol,ty::Z3_sort)
    ccall((:Z3_mk_const,testclang),Z3_ast,(Z3_context,Z3_symbol,Z3_sort),c,s,ty)
end

function Z3_mk_fresh_func_decl(c::Z3_context,prefix::Z3_string,domain_size::Uint32,domain::Ptr{Z3_sort},range::Z3_sort)
    ccall((:Z3_mk_fresh_func_decl,testclang),Z3_func_decl,(Z3_context,Z3_string,Uint32,Ptr{Z3_sort},Z3_sort),c,prefix,domain_size,domain,range)
end

function Z3_mk_fresh_const(c::Z3_context,prefix::Z3_string,ty::Z3_sort)
    ccall((:Z3_mk_fresh_const,testclang),Z3_ast,(Z3_context,Z3_string,Z3_sort),c,prefix,ty)
end

function Z3_mk_true(c::Z3_context)
    ccall((:Z3_mk_true,testclang),Z3_ast,(Z3_context,),c)
end

function Z3_mk_false(c::Z3_context)
    ccall((:Z3_mk_false,testclang),Z3_ast,(Z3_context,),c)
end

function Z3_mk_eq(c::Z3_context,l::Z3_ast,r::Z3_ast)
    ccall((:Z3_mk_eq,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,l,r)
end

function Z3_mk_distinct(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_distinct,testclang),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
end

function Z3_mk_not(c::Z3_context,a::Z3_ast)
    ccall((:Z3_mk_not,testclang),Z3_ast,(Z3_context,Z3_ast),c,a)
end

function Z3_mk_ite(c::Z3_context,t1::Z3_ast,t2::Z3_ast,t3::Z3_ast)
    ccall((:Z3_mk_ite,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast,Z3_ast),c,t1,t2,t3)
end

function Z3_mk_iff(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_iff,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_implies(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_implies,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_xor(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_xor,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_and(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_and,testclang),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
end

function Z3_mk_or(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_or,testclang),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
end

function Z3_mk_add(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_add,testclang),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
end

function Z3_mk_mul(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_mul,testclang),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
end

function Z3_mk_sub(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_sub,testclang),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
end

function Z3_mk_unary_minus(c::Z3_context,arg::Z3_ast)
    ccall((:Z3_mk_unary_minus,testclang),Z3_ast,(Z3_context,Z3_ast),c,arg)
end

function Z3_mk_div(c::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_div,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,arg1,arg2)
end

function Z3_mk_mod(c::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_mod,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,arg1,arg2)
end

function Z3_mk_rem(c::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_rem,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,arg1,arg2)
end

function Z3_mk_power(c::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_power,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,arg1,arg2)
end

function Z3_mk_lt(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_lt,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_le(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_le,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_gt(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_gt,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_ge(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_ge,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_int2real(c::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_int2real,testclang),Z3_ast,(Z3_context,Z3_ast),c,t1)
end

function Z3_mk_real2int(c::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_real2int,testclang),Z3_ast,(Z3_context,Z3_ast),c,t1)
end

function Z3_mk_is_int(c::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_is_int,testclang),Z3_ast,(Z3_context,Z3_ast),c,t1)
end

function Z3_mk_bvnot(c::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_bvnot,testclang),Z3_ast,(Z3_context,Z3_ast),c,t1)
end

function Z3_mk_bvredand(c::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_bvredand,testclang),Z3_ast,(Z3_context,Z3_ast),c,t1)
end

function Z3_mk_bvredor(c::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_bvredor,testclang),Z3_ast,(Z3_context,Z3_ast),c,t1)
end

function Z3_mk_bvand(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvand,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvor(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvor,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvxor(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvxor,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvnand(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvnand,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvnor(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvnor,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvxnor(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvxnor,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvneg(c::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_bvneg,testclang),Z3_ast,(Z3_context,Z3_ast),c,t1)
end

function Z3_mk_bvadd(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvadd,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvsub(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsub,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvmul(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvmul,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvudiv(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvudiv,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvsdiv(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsdiv,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvurem(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvurem,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvsrem(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsrem,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvsmod(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsmod,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvult(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvult,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvslt(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvslt,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvule(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvule,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvsle(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsle,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvuge(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvuge,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvsge(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsge,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvugt(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvugt,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvsgt(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsgt,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_concat(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_concat,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_extract(c::Z3_context,high::Uint32,low::Uint32,t1::Z3_ast)
    ccall((:Z3_mk_extract,testclang),Z3_ast,(Z3_context,Uint32,Uint32,Z3_ast),c,high,low,t1)
end

function Z3_mk_sign_ext(c::Z3_context,i::Uint32,t1::Z3_ast)
    ccall((:Z3_mk_sign_ext,testclang),Z3_ast,(Z3_context,Uint32,Z3_ast),c,i,t1)
end

function Z3_mk_zero_ext(c::Z3_context,i::Uint32,t1::Z3_ast)
    ccall((:Z3_mk_zero_ext,testclang),Z3_ast,(Z3_context,Uint32,Z3_ast),c,i,t1)
end

function Z3_mk_repeat(c::Z3_context,i::Uint32,t1::Z3_ast)
    ccall((:Z3_mk_repeat,testclang),Z3_ast,(Z3_context,Uint32,Z3_ast),c,i,t1)
end

function Z3_mk_bvshl(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvshl,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvlshr(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvlshr,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvashr(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvashr,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_rotate_left(c::Z3_context,i::Uint32,t1::Z3_ast)
    ccall((:Z3_mk_rotate_left,testclang),Z3_ast,(Z3_context,Uint32,Z3_ast),c,i,t1)
end

function Z3_mk_rotate_right(c::Z3_context,i::Uint32,t1::Z3_ast)
    ccall((:Z3_mk_rotate_right,testclang),Z3_ast,(Z3_context,Uint32,Z3_ast),c,i,t1)
end

function Z3_mk_ext_rotate_left(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_ext_rotate_left,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_ext_rotate_right(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_ext_rotate_right,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_int2bv(c::Z3_context,n::Uint32,t1::Z3_ast)
    ccall((:Z3_mk_int2bv,testclang),Z3_ast,(Z3_context,Uint32,Z3_ast),c,n,t1)
end

function Z3_mk_bv2int(c::Z3_context,t1::Z3_ast,is_signed::Z3_bool)
    ccall((:Z3_mk_bv2int,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_bool),c,t1,is_signed)
end

function Z3_mk_bvadd_no_overflow(c::Z3_context,t1::Z3_ast,t2::Z3_ast,is_signed::Z3_bool)
    ccall((:Z3_mk_bvadd_no_overflow,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast,Z3_bool),c,t1,t2,is_signed)
end

function Z3_mk_bvadd_no_underflow(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvadd_no_underflow,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvsub_no_overflow(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsub_no_overflow,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvsub_no_underflow(c::Z3_context,t1::Z3_ast,t2::Z3_ast,is_signed::Z3_bool)
    ccall((:Z3_mk_bvsub_no_underflow,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast,Z3_bool),c,t1,t2,is_signed)
end

function Z3_mk_bvsdiv_no_overflow(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvsdiv_no_overflow,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_bvneg_no_overflow(c::Z3_context,t1::Z3_ast)
    ccall((:Z3_mk_bvneg_no_overflow,testclang),Z3_ast,(Z3_context,Z3_ast),c,t1)
end

function Z3_mk_bvmul_no_overflow(c::Z3_context,t1::Z3_ast,t2::Z3_ast,is_signed::Z3_bool)
    ccall((:Z3_mk_bvmul_no_overflow,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast,Z3_bool),c,t1,t2,is_signed)
end

function Z3_mk_bvmul_no_underflow(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_mk_bvmul_no_underflow,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_mk_select(c::Z3_context,a::Z3_ast,i::Z3_ast)
    ccall((:Z3_mk_select,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,a,i)
end

function Z3_mk_store(c::Z3_context,a::Z3_ast,i::Z3_ast,v::Z3_ast)
    ccall((:Z3_mk_store,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast,Z3_ast),c,a,i,v)
end

function Z3_mk_const_array(c::Z3_context,domain::Z3_sort,v::Z3_ast)
    ccall((:Z3_mk_const_array,testclang),Z3_ast,(Z3_context,Z3_sort,Z3_ast),c,domain,v)
end

function Z3_mk_map(c::Z3_context,f::Z3_func_decl,n::Uint32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_map,testclang),Z3_ast,(Z3_context,Z3_func_decl,Uint32,Ptr{Z3_ast}),c,f,n,args)
end

function Z3_mk_array_default(c::Z3_context,array::Z3_ast)
    ccall((:Z3_mk_array_default,testclang),Z3_ast,(Z3_context,Z3_ast),c,array)
end

function Z3_mk_set_sort(c::Z3_context,ty::Z3_sort)
    ccall((:Z3_mk_set_sort,testclang),Z3_sort,(Z3_context,Z3_sort),c,ty)
end

function Z3_mk_empty_set(c::Z3_context,domain::Z3_sort)
    ccall((:Z3_mk_empty_set,testclang),Z3_ast,(Z3_context,Z3_sort),c,domain)
end

function Z3_mk_full_set(c::Z3_context,domain::Z3_sort)
    ccall((:Z3_mk_full_set,testclang),Z3_ast,(Z3_context,Z3_sort),c,domain)
end

function Z3_mk_set_add(c::Z3_context,set::Z3_ast,elem::Z3_ast)
    ccall((:Z3_mk_set_add,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,set,elem)
end

function Z3_mk_set_del(c::Z3_context,set::Z3_ast,elem::Z3_ast)
    ccall((:Z3_mk_set_del,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,set,elem)
end

function Z3_mk_set_union(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_set_union,testclang),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
end

function Z3_mk_set_intersect(c::Z3_context,num_args::Uint32,args::Ptr{Z3_ast})
    ccall((:Z3_mk_set_intersect,testclang),Z3_ast,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_args,args)
end

function Z3_mk_set_difference(c::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_set_difference,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,arg1,arg2)
end

function Z3_mk_set_complement(c::Z3_context,arg::Z3_ast)
    ccall((:Z3_mk_set_complement,testclang),Z3_ast,(Z3_context,Z3_ast),c,arg)
end

function Z3_mk_set_member(c::Z3_context,elem::Z3_ast,set::Z3_ast)
    ccall((:Z3_mk_set_member,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,elem,set)
end

function Z3_mk_set_subset(c::Z3_context,arg1::Z3_ast,arg2::Z3_ast)
    ccall((:Z3_mk_set_subset,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_ast),c,arg1,arg2)
end

function Z3_mk_numeral(c::Z3_context,numeral::Z3_string,ty::Z3_sort)
    ccall((:Z3_mk_numeral,testclang),Z3_ast,(Z3_context,Z3_string,Z3_sort),c,numeral,ty)
end

function Z3_mk_real(c::Z3_context,num::Cint,den::Cint)
    ccall((:Z3_mk_real,testclang),Z3_ast,(Z3_context,Cint,Cint),c,num,den)
end

function Z3_mk_int(c::Z3_context,v::Cint,ty::Z3_sort)
    ccall((:Z3_mk_int,testclang),Z3_ast,(Z3_context,Cint,Z3_sort),c,v,ty)
end

function Z3_mk_unsigned_int(c::Z3_context,v::Uint32,ty::Z3_sort)
    ccall((:Z3_mk_unsigned_int,testclang),Z3_ast,(Z3_context,Uint32,Z3_sort),c,v,ty)
end

function Z3_mk_int64(c::Z3_context,v::Clonglong,ty::Z3_sort)
    ccall((:Z3_mk_int64,testclang),Z3_ast,(Z3_context,Clonglong,Z3_sort),c,v,ty)
end

function Z3_mk_unsigned_int64(c::Z3_context,v::Culonglong,ty::Z3_sort)
    ccall((:Z3_mk_unsigned_int64,testclang),Z3_ast,(Z3_context,Culonglong,Z3_sort),c,v,ty)
end

function Z3_mk_pattern(c::Z3_context,num_patterns::Uint32,terms::Ptr{Z3_ast})
    ccall((:Z3_mk_pattern,testclang),Z3_pattern,(Z3_context,Uint32,Ptr{Z3_ast}),c,num_patterns,terms)
end

function Z3_mk_bound(c::Z3_context,index::Uint32,ty::Z3_sort)
    ccall((:Z3_mk_bound,testclang),Z3_ast,(Z3_context,Uint32,Z3_sort),c,index,ty)
end

function Z3_mk_forall(c::Z3_context,weight::Uint32,num_patterns::Uint32,patterns::Ptr{Z3_pattern},num_decls::Uint32,sorts::Ptr{Z3_sort},decl_names::Ptr{Z3_symbol},body::Z3_ast)
    ccall((:Z3_mk_forall,testclang),Z3_ast,(Z3_context,Uint32,Uint32,Ptr{Z3_pattern},Uint32,Ptr{Z3_sort},Ptr{Z3_symbol},Z3_ast),c,weight,num_patterns,patterns,num_decls,sorts,decl_names,body)
end

function Z3_mk_exists(c::Z3_context,weight::Uint32,num_patterns::Uint32,patterns::Ptr{Z3_pattern},num_decls::Uint32,sorts::Ptr{Z3_sort},decl_names::Ptr{Z3_symbol},body::Z3_ast)
    ccall((:Z3_mk_exists,testclang),Z3_ast,(Z3_context,Uint32,Uint32,Ptr{Z3_pattern},Uint32,Ptr{Z3_sort},Ptr{Z3_symbol},Z3_ast),c,weight,num_patterns,patterns,num_decls,sorts,decl_names,body)
end

function Z3_mk_quantifier(c::Z3_context,is_forall::Z3_bool,weight::Uint32,num_patterns::Uint32,patterns::Ptr{Z3_pattern},num_decls::Uint32,sorts::Ptr{Z3_sort},decl_names::Ptr{Z3_symbol},body::Z3_ast)
    ccall((:Z3_mk_quantifier,testclang),Z3_ast,(Z3_context,Z3_bool,Uint32,Uint32,Ptr{Z3_pattern},Uint32,Ptr{Z3_sort},Ptr{Z3_symbol},Z3_ast),c,is_forall,weight,num_patterns,patterns,num_decls,sorts,decl_names,body)
end

function Z3_mk_quantifier_ex(c::Z3_context,is_forall::Z3_bool,weight::Uint32,quantifier_id::Z3_symbol,skolem_id::Z3_symbol,num_patterns::Uint32,patterns::Ptr{Z3_pattern},num_no_patterns::Uint32,no_patterns::Ptr{Z3_ast},num_decls::Uint32,sorts::Ptr{Z3_sort},decl_names::Ptr{Z3_symbol},body::Z3_ast)
    ccall((:Z3_mk_quantifier_ex,testclang),Z3_ast,(Z3_context,Z3_bool,Uint32,Z3_symbol,Z3_symbol,Uint32,Ptr{Z3_pattern},Uint32,Ptr{Z3_ast},Uint32,Ptr{Z3_sort},Ptr{Z3_symbol},Z3_ast),c,is_forall,weight,quantifier_id,skolem_id,num_patterns,patterns,num_no_patterns,no_patterns,num_decls,sorts,decl_names,body)
end

function Z3_mk_forall_const(c::Z3_context,weight::Uint32,num_bound::Uint32,bound::Ptr{Z3_app},num_patterns::Uint32,patterns::Ptr{Z3_pattern},body::Z3_ast)
    ccall((:Z3_mk_forall_const,testclang),Z3_ast,(Z3_context,Uint32,Uint32,Ptr{Z3_app},Uint32,Ptr{Z3_pattern},Z3_ast),c,weight,num_bound,bound,num_patterns,patterns,body)
end

function Z3_mk_exists_const(c::Z3_context,weight::Uint32,num_bound::Uint32,bound::Ptr{Z3_app},num_patterns::Uint32,patterns::Ptr{Z3_pattern},body::Z3_ast)
    ccall((:Z3_mk_exists_const,testclang),Z3_ast,(Z3_context,Uint32,Uint32,Ptr{Z3_app},Uint32,Ptr{Z3_pattern},Z3_ast),c,weight,num_bound,bound,num_patterns,patterns,body)
end

function Z3_mk_quantifier_const(c::Z3_context,is_forall::Z3_bool,weight::Uint32,num_bound::Uint32,bound::Ptr{Z3_app},num_patterns::Uint32,patterns::Ptr{Z3_pattern},body::Z3_ast)
    ccall((:Z3_mk_quantifier_const,testclang),Z3_ast,(Z3_context,Z3_bool,Uint32,Uint32,Ptr{Z3_app},Uint32,Ptr{Z3_pattern},Z3_ast),c,is_forall,weight,num_bound,bound,num_patterns,patterns,body)
end

function Z3_mk_quantifier_const_ex(c::Z3_context,is_forall::Z3_bool,weight::Uint32,quantifier_id::Z3_symbol,skolem_id::Z3_symbol,num_bound::Uint32,bound::Ptr{Z3_app},num_patterns::Uint32,patterns::Ptr{Z3_pattern},num_no_patterns::Uint32,no_patterns::Ptr{Z3_ast},body::Z3_ast)
    ccall((:Z3_mk_quantifier_const_ex,testclang),Z3_ast,(Z3_context,Z3_bool,Uint32,Z3_symbol,Z3_symbol,Uint32,Ptr{Z3_app},Uint32,Ptr{Z3_pattern},Uint32,Ptr{Z3_ast},Z3_ast),c,is_forall,weight,quantifier_id,skolem_id,num_bound,bound,num_patterns,patterns,num_no_patterns,no_patterns,body)
end

function Z3_get_symbol_kind(c::Z3_context,s::Z3_symbol)
    ccall((:Z3_get_symbol_kind,testclang),Z3_symbol_kind,(Z3_context,Z3_symbol),c,s)
end

function Z3_get_symbol_int(c::Z3_context,s::Z3_symbol)
    ccall((:Z3_get_symbol_int,testclang),Cint,(Z3_context,Z3_symbol),c,s)
end

function Z3_get_symbol_string(c::Z3_context,s::Z3_symbol)
    ccall((:Z3_get_symbol_string,testclang),Z3_string,(Z3_context,Z3_symbol),c,s)
end

function Z3_get_sort_name(c::Z3_context,d::Z3_sort)
    ccall((:Z3_get_sort_name,testclang),Z3_symbol,(Z3_context,Z3_sort),c,d)
end

function Z3_get_sort_id(c::Z3_context,s::Z3_sort)
    ccall((:Z3_get_sort_id,testclang),Uint32,(Z3_context,Z3_sort),c,s)
end

function Z3_sort_to_ast(c::Z3_context,s::Z3_sort)
    ccall((:Z3_sort_to_ast,testclang),Z3_ast,(Z3_context,Z3_sort),c,s)
end

function Z3_is_eq_sort(c::Z3_context,s1::Z3_sort,s2::Z3_sort)
    ccall((:Z3_is_eq_sort,testclang),Z3_bool,(Z3_context,Z3_sort,Z3_sort),c,s1,s2)
end

function Z3_get_sort_kind(c::Z3_context,t::Z3_sort)
    ccall((:Z3_get_sort_kind,testclang),Z3_sort_kind,(Z3_context,Z3_sort),c,t)
end

function Z3_get_bv_sort_size(c::Z3_context,t::Z3_sort)
    ccall((:Z3_get_bv_sort_size,testclang),Uint32,(Z3_context,Z3_sort),c,t)
end

function Z3_get_finite_domain_sort_size(c::Z3_context,s::Z3_sort,r::Ptr{Culonglong})
    ccall((:Z3_get_finite_domain_sort_size,testclang),Z3_bool,(Z3_context,Z3_sort,Ptr{Culonglong}),c,s,r)
end

function Z3_get_array_sort_domain(c::Z3_context,t::Z3_sort)
    ccall((:Z3_get_array_sort_domain,testclang),Z3_sort,(Z3_context,Z3_sort),c,t)
end

function Z3_get_array_sort_range(c::Z3_context,t::Z3_sort)
    ccall((:Z3_get_array_sort_range,testclang),Z3_sort,(Z3_context,Z3_sort),c,t)
end

function Z3_get_tuple_sort_mk_decl(c::Z3_context,t::Z3_sort)
    ccall((:Z3_get_tuple_sort_mk_decl,testclang),Z3_func_decl,(Z3_context,Z3_sort),c,t)
end

function Z3_get_tuple_sort_num_fields(c::Z3_context,t::Z3_sort)
    ccall((:Z3_get_tuple_sort_num_fields,testclang),Uint32,(Z3_context,Z3_sort),c,t)
end

function Z3_get_tuple_sort_field_decl(c::Z3_context,t::Z3_sort,i::Uint32)
    ccall((:Z3_get_tuple_sort_field_decl,testclang),Z3_func_decl,(Z3_context,Z3_sort,Uint32),c,t,i)
end

function Z3_get_datatype_sort_num_constructors(c::Z3_context,t::Z3_sort)
    ccall((:Z3_get_datatype_sort_num_constructors,testclang),Uint32,(Z3_context,Z3_sort),c,t)
end

function Z3_get_datatype_sort_constructor(c::Z3_context,t::Z3_sort,idx::Uint32)
    ccall((:Z3_get_datatype_sort_constructor,testclang),Z3_func_decl,(Z3_context,Z3_sort,Uint32),c,t,idx)
end

function Z3_get_datatype_sort_recognizer(c::Z3_context,t::Z3_sort,idx::Uint32)
    ccall((:Z3_get_datatype_sort_recognizer,testclang),Z3_func_decl,(Z3_context,Z3_sort,Uint32),c,t,idx)
end

function Z3_get_datatype_sort_constructor_accessor(c::Z3_context,t::Z3_sort,idx_c::Uint32,idx_a::Uint32)
    ccall((:Z3_get_datatype_sort_constructor_accessor,testclang),Z3_func_decl,(Z3_context,Z3_sort,Uint32,Uint32),c,t,idx_c,idx_a)
end

function Z3_get_relation_arity(c::Z3_context,s::Z3_sort)
    ccall((:Z3_get_relation_arity,testclang),Uint32,(Z3_context,Z3_sort),c,s)
end

function Z3_get_relation_column(c::Z3_context,s::Z3_sort,col::Uint32)
    ccall((:Z3_get_relation_column,testclang),Z3_sort,(Z3_context,Z3_sort,Uint32),c,s,col)
end

function Z3_func_decl_to_ast(c::Z3_context,f::Z3_func_decl)
    ccall((:Z3_func_decl_to_ast,testclang),Z3_ast,(Z3_context,Z3_func_decl),c,f)
end

function Z3_is_eq_func_decl(c::Z3_context,f1::Z3_func_decl,f2::Z3_func_decl)
    ccall((:Z3_is_eq_func_decl,testclang),Z3_bool,(Z3_context,Z3_func_decl,Z3_func_decl),c,f1,f2)
end

function Z3_get_func_decl_id(c::Z3_context,f::Z3_func_decl)
    ccall((:Z3_get_func_decl_id,testclang),Uint32,(Z3_context,Z3_func_decl),c,f)
end

function Z3_get_decl_name(c::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_decl_name,testclang),Z3_symbol,(Z3_context,Z3_func_decl),c,d)
end

function Z3_get_decl_kind(c::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_decl_kind,testclang),Z3_decl_kind,(Z3_context,Z3_func_decl),c,d)
end

function Z3_get_domain_size(c::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_domain_size,testclang),Uint32,(Z3_context,Z3_func_decl),c,d)
end

function Z3_get_arity(c::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_arity,testclang),Uint32,(Z3_context,Z3_func_decl),c,d)
end

function Z3_get_domain(c::Z3_context,d::Z3_func_decl,i::Uint32)
    ccall((:Z3_get_domain,testclang),Z3_sort,(Z3_context,Z3_func_decl,Uint32),c,d,i)
end

function Z3_get_range(c::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_range,testclang),Z3_sort,(Z3_context,Z3_func_decl),c,d)
end

function Z3_get_decl_num_parameters(c::Z3_context,d::Z3_func_decl)
    ccall((:Z3_get_decl_num_parameters,testclang),Uint32,(Z3_context,Z3_func_decl),c,d)
end

function Z3_get_decl_parameter_kind(c::Z3_context,d::Z3_func_decl,idx::Uint32)
    ccall((:Z3_get_decl_parameter_kind,testclang),Z3_parameter_kind,(Z3_context,Z3_func_decl,Uint32),c,d,idx)
end

function Z3_get_decl_int_parameter(c::Z3_context,d::Z3_func_decl,idx::Uint32)
    ccall((:Z3_get_decl_int_parameter,testclang),Cint,(Z3_context,Z3_func_decl,Uint32),c,d,idx)
end

function Z3_get_decl_double_parameter(c::Z3_context,d::Z3_func_decl,idx::Uint32)
    ccall((:Z3_get_decl_double_parameter,testclang),Cdouble,(Z3_context,Z3_func_decl,Uint32),c,d,idx)
end

function Z3_get_decl_symbol_parameter(c::Z3_context,d::Z3_func_decl,idx::Uint32)
    ccall((:Z3_get_decl_symbol_parameter,testclang),Z3_symbol,(Z3_context,Z3_func_decl,Uint32),c,d,idx)
end

function Z3_get_decl_sort_parameter(c::Z3_context,d::Z3_func_decl,idx::Uint32)
    ccall((:Z3_get_decl_sort_parameter,testclang),Z3_sort,(Z3_context,Z3_func_decl,Uint32),c,d,idx)
end

function Z3_get_decl_ast_parameter(c::Z3_context,d::Z3_func_decl,idx::Uint32)
    ccall((:Z3_get_decl_ast_parameter,testclang),Z3_ast,(Z3_context,Z3_func_decl,Uint32),c,d,idx)
end

function Z3_get_decl_func_decl_parameter(c::Z3_context,d::Z3_func_decl,idx::Uint32)
    ccall((:Z3_get_decl_func_decl_parameter,testclang),Z3_func_decl,(Z3_context,Z3_func_decl,Uint32),c,d,idx)
end

function Z3_get_decl_rational_parameter(c::Z3_context,d::Z3_func_decl,idx::Uint32)
    ccall((:Z3_get_decl_rational_parameter,testclang),Z3_string,(Z3_context,Z3_func_decl,Uint32),c,d,idx)
end

function Z3_app_to_ast(c::Z3_context,a::Z3_app)
    ccall((:Z3_app_to_ast,testclang),Z3_ast,(Z3_context,Z3_app),c,a)
end

function Z3_get_app_decl(c::Z3_context,a::Z3_app)
    ccall((:Z3_get_app_decl,testclang),Z3_func_decl,(Z3_context,Z3_app),c,a)
end

function Z3_get_app_num_args(c::Z3_context,a::Z3_app)
    ccall((:Z3_get_app_num_args,testclang),Uint32,(Z3_context,Z3_app),c,a)
end

function Z3_get_app_arg(c::Z3_context,a::Z3_app,i::Uint32)
    ccall((:Z3_get_app_arg,testclang),Z3_ast,(Z3_context,Z3_app,Uint32),c,a,i)
end

function Z3_is_eq_ast(c::Z3_context,t1::Z3_ast,t2::Z3_ast)
    ccall((:Z3_is_eq_ast,testclang),Z3_bool,(Z3_context,Z3_ast,Z3_ast),c,t1,t2)
end

function Z3_get_ast_id(c::Z3_context,t::Z3_ast)
    ccall((:Z3_get_ast_id,testclang),Uint32,(Z3_context,Z3_ast),c,t)
end

function Z3_get_ast_hash(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_ast_hash,testclang),Uint32,(Z3_context,Z3_ast),c,a)
end

function Z3_get_sort(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_sort,testclang),Z3_sort,(Z3_context,Z3_ast),c,a)
end

function Z3_is_well_sorted(c::Z3_context,t::Z3_ast)
    ccall((:Z3_is_well_sorted,testclang),Z3_bool,(Z3_context,Z3_ast),c,t)
end

function Z3_get_bool_value(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_bool_value,testclang),Z3_lbool,(Z3_context,Z3_ast),c,a)
end

function Z3_get_ast_kind(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_ast_kind,testclang),Z3_ast_kind,(Z3_context,Z3_ast),c,a)
end

function Z3_is_app(c::Z3_context,a::Z3_ast)
    ccall((:Z3_is_app,testclang),Z3_bool,(Z3_context,Z3_ast),c,a)
end

function Z3_is_numeral_ast(c::Z3_context,a::Z3_ast)
    ccall((:Z3_is_numeral_ast,testclang),Z3_bool,(Z3_context,Z3_ast),c,a)
end

function Z3_is_algebraic_number(c::Z3_context,a::Z3_ast)
    ccall((:Z3_is_algebraic_number,testclang),Z3_bool,(Z3_context,Z3_ast),c,a)
end

function Z3_to_app(c::Z3_context,a::Z3_ast)
    ccall((:Z3_to_app,testclang),Z3_app,(Z3_context,Z3_ast),c,a)
end

function Z3_to_func_decl(c::Z3_context,a::Z3_ast)
    ccall((:Z3_to_func_decl,testclang),Z3_func_decl,(Z3_context,Z3_ast),c,a)
end

function Z3_get_numeral_string(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_numeral_string,testclang),Z3_string,(Z3_context,Z3_ast),c,a)
end

function Z3_get_numeral_decimal_string(c::Z3_context,a::Z3_ast,precision::Uint32)
    ccall((:Z3_get_numeral_decimal_string,testclang),Z3_string,(Z3_context,Z3_ast,Uint32),c,a,precision)
end

function Z3_get_numerator(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_numerator,testclang),Z3_ast,(Z3_context,Z3_ast),c,a)
end

function Z3_get_denominator(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_denominator,testclang),Z3_ast,(Z3_context,Z3_ast),c,a)
end

function Z3_get_numeral_small(c::Z3_context,a::Z3_ast,num::Ptr{Clonglong},den::Ptr{Clonglong})
    ccall((:Z3_get_numeral_small,testclang),Z3_bool,(Z3_context,Z3_ast,Ptr{Clonglong},Ptr{Clonglong}),c,a,num,den)
end

function Z3_get_numeral_int(c::Z3_context,v::Z3_ast,i::Ptr{Cint})
    ccall((:Z3_get_numeral_int,testclang),Z3_bool,(Z3_context,Z3_ast,Ptr{Cint}),c,v,i)
end

function Z3_get_numeral_uint(c::Z3_context,v::Z3_ast,u::Ptr{Uint32})
    ccall((:Z3_get_numeral_uint,testclang),Z3_bool,(Z3_context,Z3_ast,Ptr{Uint32}),c,v,u)
end

function Z3_get_numeral_uint64(c::Z3_context,v::Z3_ast,u::Ptr{Culonglong})
    ccall((:Z3_get_numeral_uint64,testclang),Z3_bool,(Z3_context,Z3_ast,Ptr{Culonglong}),c,v,u)
end

function Z3_get_numeral_int64(c::Z3_context,v::Z3_ast,i::Ptr{Clonglong})
    ccall((:Z3_get_numeral_int64,testclang),Z3_bool,(Z3_context,Z3_ast,Ptr{Clonglong}),c,v,i)
end

function Z3_get_numeral_rational_int64(c::Z3_context,v::Z3_ast,num::Ptr{Clonglong},den::Ptr{Clonglong})
    ccall((:Z3_get_numeral_rational_int64,testclang),Z3_bool,(Z3_context,Z3_ast,Ptr{Clonglong},Ptr{Clonglong}),c,v,num,den)
end

function Z3_get_algebraic_number_lower(c::Z3_context,a::Z3_ast,precision::Uint32)
    ccall((:Z3_get_algebraic_number_lower,testclang),Z3_ast,(Z3_context,Z3_ast,Uint32),c,a,precision)
end

function Z3_get_algebraic_number_upper(c::Z3_context,a::Z3_ast,precision::Uint32)
    ccall((:Z3_get_algebraic_number_upper,testclang),Z3_ast,(Z3_context,Z3_ast,Uint32),c,a,precision)
end

function Z3_pattern_to_ast(c::Z3_context,p::Z3_pattern)
    ccall((:Z3_pattern_to_ast,testclang),Z3_ast,(Z3_context,Z3_pattern),c,p)
end

function Z3_get_pattern_num_terms(c::Z3_context,p::Z3_pattern)
    ccall((:Z3_get_pattern_num_terms,testclang),Uint32,(Z3_context,Z3_pattern),c,p)
end

function Z3_get_pattern(c::Z3_context,p::Z3_pattern,idx::Uint32)
    ccall((:Z3_get_pattern,testclang),Z3_ast,(Z3_context,Z3_pattern,Uint32),c,p,idx)
end

function Z3_get_index_value(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_index_value,testclang),Uint32,(Z3_context,Z3_ast),c,a)
end

function Z3_is_quantifier_forall(c::Z3_context,a::Z3_ast)
    ccall((:Z3_is_quantifier_forall,testclang),Z3_bool,(Z3_context,Z3_ast),c,a)
end

function Z3_get_quantifier_weight(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_quantifier_weight,testclang),Uint32,(Z3_context,Z3_ast),c,a)
end

function Z3_get_quantifier_num_patterns(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_quantifier_num_patterns,testclang),Uint32,(Z3_context,Z3_ast),c,a)
end

function Z3_get_quantifier_pattern_ast(c::Z3_context,a::Z3_ast,i::Uint32)
    ccall((:Z3_get_quantifier_pattern_ast,testclang),Z3_pattern,(Z3_context,Z3_ast,Uint32),c,a,i)
end

function Z3_get_quantifier_num_no_patterns(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_quantifier_num_no_patterns,testclang),Uint32,(Z3_context,Z3_ast),c,a)
end

function Z3_get_quantifier_no_pattern_ast(c::Z3_context,a::Z3_ast,i::Uint32)
    ccall((:Z3_get_quantifier_no_pattern_ast,testclang),Z3_ast,(Z3_context,Z3_ast,Uint32),c,a,i)
end

function Z3_get_quantifier_num_bound(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_quantifier_num_bound,testclang),Uint32,(Z3_context,Z3_ast),c,a)
end

function Z3_get_quantifier_bound_name(c::Z3_context,a::Z3_ast,i::Uint32)
    ccall((:Z3_get_quantifier_bound_name,testclang),Z3_symbol,(Z3_context,Z3_ast,Uint32),c,a,i)
end

function Z3_get_quantifier_bound_sort(c::Z3_context,a::Z3_ast,i::Uint32)
    ccall((:Z3_get_quantifier_bound_sort,testclang),Z3_sort,(Z3_context,Z3_ast,Uint32),c,a,i)
end

function Z3_get_quantifier_body(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_quantifier_body,testclang),Z3_ast,(Z3_context,Z3_ast),c,a)
end

function Z3_simplify(c::Z3_context,a::Z3_ast)
    ccall((:Z3_simplify,testclang),Z3_ast,(Z3_context,Z3_ast),c,a)
end

function Z3_simplify_ex(c::Z3_context,a::Z3_ast,p::Z3_params)
    ccall((:Z3_simplify_ex,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_params),c,a,p)
end

function Z3_simplify_get_help(c::Z3_context)
    ccall((:Z3_simplify_get_help,testclang),Z3_string,(Z3_context,),c)
end

function Z3_simplify_get_param_descrs(c::Z3_context)
    ccall((:Z3_simplify_get_param_descrs,testclang),Z3_param_descrs,(Z3_context,),c)
end

function Z3_update_term(c::Z3_context,a::Z3_ast,num_args::Uint32,args::Ptr{Z3_ast})
    ccall((:Z3_update_term,testclang),Z3_ast,(Z3_context,Z3_ast,Uint32,Ptr{Z3_ast}),c,a,num_args,args)
end

function Z3_substitute(c::Z3_context,a::Z3_ast,num_exprs::Uint32,from::Ptr{Z3_ast},to::Ptr{Z3_ast})
    ccall((:Z3_substitute,testclang),Z3_ast,(Z3_context,Z3_ast,Uint32,Ptr{Z3_ast},Ptr{Z3_ast}),c,a,num_exprs,from,to)
end

function Z3_substitute_vars(c::Z3_context,a::Z3_ast,num_exprs::Uint32,to::Ptr{Z3_ast})
    ccall((:Z3_substitute_vars,testclang),Z3_ast,(Z3_context,Z3_ast,Uint32,Ptr{Z3_ast}),c,a,num_exprs,to)
end

function Z3_translate(source::Z3_context,a::Z3_ast,target::Z3_context)
    ccall((:Z3_translate,testclang),Z3_ast,(Z3_context,Z3_ast,Z3_context),source,a,target)
end

function Z3_model_inc_ref(c::Z3_context,m::Z3_model)
    ccall((:Z3_model_inc_ref,testclang),Void,(Z3_context,Z3_model),c,m)
end

function Z3_model_dec_ref(c::Z3_context,m::Z3_model)
    ccall((:Z3_model_dec_ref,testclang),Void,(Z3_context,Z3_model),c,m)
end

function Z3_model_eval(c::Z3_context,m::Z3_model,t::Z3_ast,model_completion::Z3_bool,v::Ptr{Z3_ast})
    ccall((:Z3_model_eval,testclang),Z3_bool,(Z3_context,Z3_model,Z3_ast,Z3_bool,Ptr{Z3_ast}),c,m,t,model_completion,v)
end

function Z3_model_get_const_interp(c::Z3_context,m::Z3_model,a::Z3_func_decl)
    ccall((:Z3_model_get_const_interp,testclang),Z3_ast,(Z3_context,Z3_model,Z3_func_decl),c,m,a)
end

function Z3_model_has_interp(c::Z3_context,m::Z3_model,a::Z3_func_decl)
    ccall((:Z3_model_has_interp,testclang),Z3_bool,(Z3_context,Z3_model,Z3_func_decl),c,m,a)
end

function Z3_model_get_func_interp(c::Z3_context,m::Z3_model,f::Z3_func_decl)
    ccall((:Z3_model_get_func_interp,testclang),Z3_func_interp,(Z3_context,Z3_model,Z3_func_decl),c,m,f)
end

function Z3_model_get_num_consts(c::Z3_context,m::Z3_model)
    ccall((:Z3_model_get_num_consts,testclang),Uint32,(Z3_context,Z3_model),c,m)
end

function Z3_model_get_const_decl(c::Z3_context,m::Z3_model,i::Uint32)
    ccall((:Z3_model_get_const_decl,testclang),Z3_func_decl,(Z3_context,Z3_model,Uint32),c,m,i)
end

function Z3_model_get_num_funcs(c::Z3_context,m::Z3_model)
    ccall((:Z3_model_get_num_funcs,testclang),Uint32,(Z3_context,Z3_model),c,m)
end

function Z3_model_get_func_decl(c::Z3_context,m::Z3_model,i::Uint32)
    ccall((:Z3_model_get_func_decl,testclang),Z3_func_decl,(Z3_context,Z3_model,Uint32),c,m,i)
end

function Z3_model_get_num_sorts(c::Z3_context,m::Z3_model)
    ccall((:Z3_model_get_num_sorts,testclang),Uint32,(Z3_context,Z3_model),c,m)
end

function Z3_model_get_sort(c::Z3_context,m::Z3_model,i::Uint32)
    ccall((:Z3_model_get_sort,testclang),Z3_sort,(Z3_context,Z3_model,Uint32),c,m,i)
end

function Z3_model_get_sort_universe(c::Z3_context,m::Z3_model,s::Z3_sort)
    ccall((:Z3_model_get_sort_universe,testclang),Z3_ast_vector,(Z3_context,Z3_model,Z3_sort),c,m,s)
end

function Z3_is_as_array(c::Z3_context,a::Z3_ast)
    ccall((:Z3_is_as_array,testclang),Z3_bool,(Z3_context,Z3_ast),c,a)
end

function Z3_get_as_array_func_decl(c::Z3_context,a::Z3_ast)
    ccall((:Z3_get_as_array_func_decl,testclang),Z3_func_decl,(Z3_context,Z3_ast),c,a)
end

function Z3_func_interp_inc_ref(c::Z3_context,f::Z3_func_interp)
    ccall((:Z3_func_interp_inc_ref,testclang),Void,(Z3_context,Z3_func_interp),c,f)
end

function Z3_func_interp_dec_ref(c::Z3_context,f::Z3_func_interp)
    ccall((:Z3_func_interp_dec_ref,testclang),Void,(Z3_context,Z3_func_interp),c,f)
end

function Z3_func_interp_get_num_entries(c::Z3_context,f::Z3_func_interp)
    ccall((:Z3_func_interp_get_num_entries,testclang),Uint32,(Z3_context,Z3_func_interp),c,f)
end

function Z3_func_interp_get_entry(c::Z3_context,f::Z3_func_interp,i::Uint32)
    ccall((:Z3_func_interp_get_entry,testclang),Z3_func_entry,(Z3_context,Z3_func_interp,Uint32),c,f,i)
end

function Z3_func_interp_get_else(c::Z3_context,f::Z3_func_interp)
    ccall((:Z3_func_interp_get_else,testclang),Z3_ast,(Z3_context,Z3_func_interp),c,f)
end

function Z3_func_interp_get_arity(c::Z3_context,f::Z3_func_interp)
    ccall((:Z3_func_interp_get_arity,testclang),Uint32,(Z3_context,Z3_func_interp),c,f)
end

function Z3_func_entry_inc_ref(c::Z3_context,e::Z3_func_entry)
    ccall((:Z3_func_entry_inc_ref,testclang),Void,(Z3_context,Z3_func_entry),c,e)
end

function Z3_func_entry_dec_ref(c::Z3_context,e::Z3_func_entry)
    ccall((:Z3_func_entry_dec_ref,testclang),Void,(Z3_context,Z3_func_entry),c,e)
end

function Z3_func_entry_get_value(c::Z3_context,e::Z3_func_entry)
    ccall((:Z3_func_entry_get_value,testclang),Z3_ast,(Z3_context,Z3_func_entry),c,e)
end

function Z3_func_entry_get_num_args(c::Z3_context,e::Z3_func_entry)
    ccall((:Z3_func_entry_get_num_args,testclang),Uint32,(Z3_context,Z3_func_entry),c,e)
end

function Z3_func_entry_get_arg(c::Z3_context,e::Z3_func_entry,i::Uint32)
    ccall((:Z3_func_entry_get_arg,testclang),Z3_ast,(Z3_context,Z3_func_entry,Uint32),c,e,i)
end

function Z3_open_log(filename::Z3_string)
    ccall((:Z3_open_log,testclang),Z3_bool,(Z3_string,),filename)
end

function Z3_append_log(string::Z3_string)
    ccall((:Z3_append_log,testclang),Void,(Z3_string,),string)
end

function Z3_close_log()
    ccall((:Z3_close_log,testclang),Void,())
end

function Z3_toggle_warning_messages(enabled::Z3_bool)
    ccall((:Z3_toggle_warning_messages,testclang),Void,(Z3_bool,),enabled)
end

function Z3_set_ast_print_mode(c::Z3_context,mode::Z3_ast_print_mode)
    ccall((:Z3_set_ast_print_mode,testclang),Void,(Z3_context,Z3_ast_print_mode),c,mode)
end

function Z3_ast_to_string(c::Z3_context,a::Z3_ast)
    ccall((:Z3_ast_to_string,testclang),Z3_string,(Z3_context,Z3_ast),c,a)
end

function Z3_pattern_to_string(c::Z3_context,p::Z3_pattern)
    ccall((:Z3_pattern_to_string,testclang),Z3_string,(Z3_context,Z3_pattern),c,p)
end

function Z3_sort_to_string(c::Z3_context,s::Z3_sort)
    ccall((:Z3_sort_to_string,testclang),Z3_string,(Z3_context,Z3_sort),c,s)
end

function Z3_func_decl_to_string(c::Z3_context,d::Z3_func_decl)
    ccall((:Z3_func_decl_to_string,testclang),Z3_string,(Z3_context,Z3_func_decl),c,d)
end

function Z3_model_to_string(c::Z3_context,m::Z3_model)
    ccall((:Z3_model_to_string,testclang),Z3_string,(Z3_context,Z3_model),c,m)
end

function Z3_benchmark_to_smtlib_string(c::Z3_context,name::Z3_string,logic::Z3_string,status::Z3_string,attributes::Z3_string,num_assumptions::Uint32,assumptions::Ptr{Z3_ast},formula::Z3_ast)
    ccall((:Z3_benchmark_to_smtlib_string,testclang),Z3_string,(Z3_context,Z3_string,Z3_string,Z3_string,Z3_string,Uint32,Ptr{Z3_ast},Z3_ast),c,name,logic,status,attributes,num_assumptions,assumptions,formula)
end

function Z3_parse_smtlib2_string(c::Z3_context,str::Z3_string,num_sorts::Uint32,sort_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},num_decls::Uint32,decl_names::Ptr{Z3_symbol},decls::Ptr{Z3_func_decl})
    ccall((:Z3_parse_smtlib2_string,testclang),Z3_ast,(Z3_context,Z3_string,Uint32,Ptr{Z3_symbol},Ptr{Z3_sort},Uint32,Ptr{Z3_symbol},Ptr{Z3_func_decl}),c,str,num_sorts,sort_names,sorts,num_decls,decl_names,decls)
end

function Z3_parse_smtlib2_file(c::Z3_context,file_name::Z3_string,num_sorts::Uint32,sort_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},num_decls::Uint32,decl_names::Ptr{Z3_symbol},decls::Ptr{Z3_func_decl})
    ccall((:Z3_parse_smtlib2_file,testclang),Z3_ast,(Z3_context,Z3_string,Uint32,Ptr{Z3_symbol},Ptr{Z3_sort},Uint32,Ptr{Z3_symbol},Ptr{Z3_func_decl}),c,file_name,num_sorts,sort_names,sorts,num_decls,decl_names,decls)
end

function Z3_parse_smtlib_string(c::Z3_context,str::Z3_string,num_sorts::Uint32,sort_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},num_decls::Uint32,decl_names::Ptr{Z3_symbol},decls::Ptr{Z3_func_decl})
    ccall((:Z3_parse_smtlib_string,testclang),Void,(Z3_context,Z3_string,Uint32,Ptr{Z3_symbol},Ptr{Z3_sort},Uint32,Ptr{Z3_symbol},Ptr{Z3_func_decl}),c,str,num_sorts,sort_names,sorts,num_decls,decl_names,decls)
end

function Z3_parse_smtlib_file(c::Z3_context,file_name::Z3_string,num_sorts::Uint32,sort_names::Ptr{Z3_symbol},sorts::Ptr{Z3_sort},num_decls::Uint32,decl_names::Ptr{Z3_symbol},decls::Ptr{Z3_func_decl})
    ccall((:Z3_parse_smtlib_file,testclang),Void,(Z3_context,Z3_string,Uint32,Ptr{Z3_symbol},Ptr{Z3_sort},Uint32,Ptr{Z3_symbol},Ptr{Z3_func_decl}),c,file_name,num_sorts,sort_names,sorts,num_decls,decl_names,decls)
end

function Z3_get_smtlib_num_formulas(c::Z3_context)
    ccall((:Z3_get_smtlib_num_formulas,testclang),Uint32,(Z3_context,),c)
end

function Z3_get_smtlib_formula(c::Z3_context,i::Uint32)
    ccall((:Z3_get_smtlib_formula,testclang),Z3_ast,(Z3_context,Uint32),c,i)
end

function Z3_get_smtlib_num_assumptions(c::Z3_context)
    ccall((:Z3_get_smtlib_num_assumptions,testclang),Uint32,(Z3_context,),c)
end

function Z3_get_smtlib_assumption(c::Z3_context,i::Uint32)
    ccall((:Z3_get_smtlib_assumption,testclang),Z3_ast,(Z3_context,Uint32),c,i)
end

function Z3_get_smtlib_num_decls(c::Z3_context)
    ccall((:Z3_get_smtlib_num_decls,testclang),Uint32,(Z3_context,),c)
end

function Z3_get_smtlib_decl(c::Z3_context,i::Uint32)
    ccall((:Z3_get_smtlib_decl,testclang),Z3_func_decl,(Z3_context,Uint32),c,i)
end

function Z3_get_smtlib_num_sorts(c::Z3_context)
    ccall((:Z3_get_smtlib_num_sorts,testclang),Uint32,(Z3_context,),c)
end

function Z3_get_smtlib_sort(c::Z3_context,i::Uint32)
    ccall((:Z3_get_smtlib_sort,testclang),Z3_sort,(Z3_context,Uint32),c,i)
end

function Z3_get_smtlib_error(c::Z3_context)
    ccall((:Z3_get_smtlib_error,testclang),Z3_string,(Z3_context,),c)
end

function Z3_get_error_code(c::Z3_context)
    ccall((:Z3_get_error_code,testclang),Z3_error_code,(Z3_context,),c)
end

function Z3_set_error_handler(c::Z3_context,h::Z3_error_handler)
    ccall((:Z3_set_error_handler,testclang),Void,(Z3_context,Z3_error_handler),c,h)
end

function Z3_set_error(c::Z3_context,e::Z3_error_code)
    ccall((:Z3_set_error,testclang),Void,(Z3_context,Z3_error_code),c,e)
end

function Z3_get_error_msg(err::Z3_error_code)
    ccall((:Z3_get_error_msg,testclang),Z3_string,(Z3_error_code,),err)
end

function Z3_get_error_msg_ex(c::Z3_context,err::Z3_error_code)
    ccall((:Z3_get_error_msg_ex,testclang),Z3_string,(Z3_context,Z3_error_code),c,err)
end

function Z3_get_version(major::Ptr{Uint32},minor::Ptr{Uint32},build_number::Ptr{Uint32},revision_number::Ptr{Uint32})
    ccall((:Z3_get_version,testclang),Void,(Ptr{Uint32},Ptr{Uint32},Ptr{Uint32},Ptr{Uint32}),major,minor,build_number,revision_number)
end

function Z3_enable_trace(tag::Z3_string)
    ccall((:Z3_enable_trace,testclang),Void,(Z3_string,),tag)
end

function Z3_disable_trace(tag::Z3_string)
    ccall((:Z3_disable_trace,testclang),Void,(Z3_string,),tag)
end

function Z3_reset_memory()
    ccall((:Z3_reset_memory,testclang),Void,())
end

function Z3_mk_theory(c::Z3_context,th_name::Z3_string,data::Z3_theory_data)
    ccall((:Z3_mk_theory,testclang),Z3_theory,(Z3_context,Z3_string,Z3_theory_data),c,th_name,data)
end

function Z3_theory_get_ext_data(t::Z3_theory)
    ccall((:Z3_theory_get_ext_data,testclang),Z3_theory_data,(Z3_theory,),t)
end

function Z3_theory_mk_sort(c::Z3_context,t::Z3_theory,s::Z3_symbol)
    ccall((:Z3_theory_mk_sort,testclang),Z3_sort,(Z3_context,Z3_theory,Z3_symbol),c,t,s)
end

function Z3_theory_mk_value(c::Z3_context,t::Z3_theory,n::Z3_symbol,s::Z3_sort)
    ccall((:Z3_theory_mk_value,testclang),Z3_ast,(Z3_context,Z3_theory,Z3_symbol,Z3_sort),c,t,n,s)
end

function Z3_theory_mk_constant(c::Z3_context,t::Z3_theory,n::Z3_symbol,s::Z3_sort)
    ccall((:Z3_theory_mk_constant,testclang),Z3_ast,(Z3_context,Z3_theory,Z3_symbol,Z3_sort),c,t,n,s)
end

function Z3_theory_mk_func_decl(c::Z3_context,t::Z3_theory,n::Z3_symbol,domain_size::Uint32,domain::Ptr{Z3_sort},range::Z3_sort)
    ccall((:Z3_theory_mk_func_decl,testclang),Z3_func_decl,(Z3_context,Z3_theory,Z3_symbol,Uint32,Ptr{Z3_sort},Z3_sort),c,t,n,domain_size,domain,range)
end

function Z3_theory_get_context(t::Z3_theory)
    ccall((:Z3_theory_get_context,testclang),Z3_context,(Z3_theory,),t)
end

function Z3_set_delete_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_delete_callback,testclang),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

function Z3_set_reduce_app_callback(t::Z3_theory,f::Z3_reduce_app_callback_fptr)
    ccall((:Z3_set_reduce_app_callback,testclang),Void,(Z3_theory,Z3_reduce_app_callback_fptr),t,f)
end

function Z3_set_reduce_eq_callback(t::Z3_theory,f::Z3_reduce_eq_callback_fptr)
    ccall((:Z3_set_reduce_eq_callback,testclang),Void,(Z3_theory,Z3_reduce_eq_callback_fptr),t,f)
end

function Z3_set_reduce_distinct_callback(t::Z3_theory,f::Z3_reduce_distinct_callback_fptr)
    ccall((:Z3_set_reduce_distinct_callback,testclang),Void,(Z3_theory,Z3_reduce_distinct_callback_fptr),t,f)
end

function Z3_set_new_app_callback(t::Z3_theory,f::Z3_theory_ast_callback_fptr)
    ccall((:Z3_set_new_app_callback,testclang),Void,(Z3_theory,Z3_theory_ast_callback_fptr),t,f)
end

function Z3_set_new_elem_callback(t::Z3_theory,f::Z3_theory_ast_callback_fptr)
    ccall((:Z3_set_new_elem_callback,testclang),Void,(Z3_theory,Z3_theory_ast_callback_fptr),t,f)
end

function Z3_set_init_search_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_init_search_callback,testclang),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

function Z3_set_push_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_push_callback,testclang),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

function Z3_set_pop_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_pop_callback,testclang),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

function Z3_set_restart_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_restart_callback,testclang),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

function Z3_set_reset_callback(t::Z3_theory,f::Z3_theory_callback_fptr)
    ccall((:Z3_set_reset_callback,testclang),Void,(Z3_theory,Z3_theory_callback_fptr),t,f)
end

function Z3_set_final_check_callback(t::Z3_theory,f::Z3_theory_final_check_callback_fptr)
    ccall((:Z3_set_final_check_callback,testclang),Void,(Z3_theory,Z3_theory_final_check_callback_fptr),t,f)
end

function Z3_set_new_eq_callback(t::Z3_theory,f::Z3_theory_ast_ast_callback_fptr)
    ccall((:Z3_set_new_eq_callback,testclang),Void,(Z3_theory,Z3_theory_ast_ast_callback_fptr),t,f)
end

function Z3_set_new_diseq_callback(t::Z3_theory,f::Z3_theory_ast_ast_callback_fptr)
    ccall((:Z3_set_new_diseq_callback,testclang),Void,(Z3_theory,Z3_theory_ast_ast_callback_fptr),t,f)
end

function Z3_set_new_assignment_callback(t::Z3_theory,f::Z3_theory_ast_bool_callback_fptr)
    ccall((:Z3_set_new_assignment_callback,testclang),Void,(Z3_theory,Z3_theory_ast_bool_callback_fptr),t,f)
end

function Z3_set_new_relevant_callback(t::Z3_theory,f::Z3_theory_ast_callback_fptr)
    ccall((:Z3_set_new_relevant_callback,testclang),Void,(Z3_theory,Z3_theory_ast_callback_fptr),t,f)
end

function Z3_theory_assert_axiom(t::Z3_theory,ax::Z3_ast)
    ccall((:Z3_theory_assert_axiom,testclang),Void,(Z3_theory,Z3_ast),t,ax)
end

function Z3_theory_assume_eq(t::Z3_theory,lhs::Z3_ast,rhs::Z3_ast)
    ccall((:Z3_theory_assume_eq,testclang),Void,(Z3_theory,Z3_ast,Z3_ast),t,lhs,rhs)
end

function Z3_theory_enable_axiom_simplification(t::Z3_theory,flag::Z3_bool)
    ccall((:Z3_theory_enable_axiom_simplification,testclang),Void,(Z3_theory,Z3_bool),t,flag)
end

function Z3_theory_get_eqc_root(t::Z3_theory,n::Z3_ast)
    ccall((:Z3_theory_get_eqc_root,testclang),Z3_ast,(Z3_theory,Z3_ast),t,n)
end

function Z3_theory_get_eqc_next(t::Z3_theory,n::Z3_ast)
    ccall((:Z3_theory_get_eqc_next,testclang),Z3_ast,(Z3_theory,Z3_ast),t,n)
end

function Z3_theory_get_num_parents(t::Z3_theory,n::Z3_ast)
    ccall((:Z3_theory_get_num_parents,testclang),Uint32,(Z3_theory,Z3_ast),t,n)
end

function Z3_theory_get_parent(t::Z3_theory,n::Z3_ast,i::Uint32)
    ccall((:Z3_theory_get_parent,testclang),Z3_ast,(Z3_theory,Z3_ast,Uint32),t,n,i)
end

function Z3_theory_is_value(t::Z3_theory,n::Z3_ast)
    ccall((:Z3_theory_is_value,testclang),Z3_bool,(Z3_theory,Z3_ast),t,n)
end

function Z3_theory_is_decl(t::Z3_theory,d::Z3_func_decl)
    ccall((:Z3_theory_is_decl,testclang),Z3_bool,(Z3_theory,Z3_func_decl),t,d)
end

function Z3_theory_get_num_elems(t::Z3_theory)
    ccall((:Z3_theory_get_num_elems,testclang),Uint32,(Z3_theory,),t)
end

function Z3_theory_get_elem(t::Z3_theory,i::Uint32)
    ccall((:Z3_theory_get_elem,testclang),Z3_ast,(Z3_theory,Uint32),t,i)
end

function Z3_theory_get_num_apps(t::Z3_theory)
    ccall((:Z3_theory_get_num_apps,testclang),Uint32,(Z3_theory,),t)
end

function Z3_theory_get_app(t::Z3_theory,i::Uint32)
    ccall((:Z3_theory_get_app,testclang),Z3_ast,(Z3_theory,Uint32),t,i)
end

function Z3_mk_fixedpoint(c::Z3_context)
    ccall((:Z3_mk_fixedpoint,testclang),Z3_fixedpoint,(Z3_context,),c)
end

function Z3_fixedpoint_inc_ref(c::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_inc_ref,testclang),Void,(Z3_context,Z3_fixedpoint),c,d)
end

function Z3_fixedpoint_dec_ref(c::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_dec_ref,testclang),Void,(Z3_context,Z3_fixedpoint),c,d)
end

function Z3_fixedpoint_add_rule(c::Z3_context,d::Z3_fixedpoint,rule::Z3_ast,name::Z3_symbol)
    ccall((:Z3_fixedpoint_add_rule,testclang),Void,(Z3_context,Z3_fixedpoint,Z3_ast,Z3_symbol),c,d,rule,name)
end

function Z3_fixedpoint_add_fact(c::Z3_context,d::Z3_fixedpoint,r::Z3_func_decl,num_args::Uint32,args::Ptr{Uint32})
    ccall((:Z3_fixedpoint_add_fact,testclang),Void,(Z3_context,Z3_fixedpoint,Z3_func_decl,Uint32,Ptr{Uint32}),c,d,r,num_args,args)
end

function Z3_fixedpoint_assert(c::Z3_context,d::Z3_fixedpoint,axiom::Z3_ast)
    ccall((:Z3_fixedpoint_assert,testclang),Void,(Z3_context,Z3_fixedpoint,Z3_ast),c,d,axiom)
end

function Z3_fixedpoint_query(c::Z3_context,d::Z3_fixedpoint,query::Z3_ast)
    ccall((:Z3_fixedpoint_query,testclang),Z3_lbool,(Z3_context,Z3_fixedpoint,Z3_ast),c,d,query)
end

function Z3_fixedpoint_query_relations(c::Z3_context,d::Z3_fixedpoint,num_relations::Uint32,relations::Ptr{Z3_func_decl})
    ccall((:Z3_fixedpoint_query_relations,testclang),Z3_lbool,(Z3_context,Z3_fixedpoint,Uint32,Ptr{Z3_func_decl}),c,d,num_relations,relations)
end

function Z3_fixedpoint_get_answer(c::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_answer,testclang),Z3_ast,(Z3_context,Z3_fixedpoint),c,d)
end

function Z3_fixedpoint_get_reason_unknown(c::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_reason_unknown,testclang),Z3_string,(Z3_context,Z3_fixedpoint),c,d)
end

function Z3_fixedpoint_update_rule(c::Z3_context,d::Z3_fixedpoint,a::Z3_ast,name::Z3_symbol)
    ccall((:Z3_fixedpoint_update_rule,testclang),Void,(Z3_context,Z3_fixedpoint,Z3_ast,Z3_symbol),c,d,a,name)
end

function Z3_fixedpoint_get_num_levels(c::Z3_context,d::Z3_fixedpoint,pred::Z3_func_decl)
    ccall((:Z3_fixedpoint_get_num_levels,testclang),Uint32,(Z3_context,Z3_fixedpoint,Z3_func_decl),c,d,pred)
end

function Z3_fixedpoint_get_cover_delta(c::Z3_context,d::Z3_fixedpoint,level::Cint,pred::Z3_func_decl)
    ccall((:Z3_fixedpoint_get_cover_delta,testclang),Z3_ast,(Z3_context,Z3_fixedpoint,Cint,Z3_func_decl),c,d,level,pred)
end

function Z3_fixedpoint_add_cover(c::Z3_context,d::Z3_fixedpoint,level::Cint,pred::Z3_func_decl,property::Z3_ast)
    ccall((:Z3_fixedpoint_add_cover,testclang),Void,(Z3_context,Z3_fixedpoint,Cint,Z3_func_decl,Z3_ast),c,d,level,pred,property)
end

function Z3_fixedpoint_get_statistics(c::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_statistics,testclang),Z3_stats,(Z3_context,Z3_fixedpoint),c,d)
end

function Z3_fixedpoint_register_relation(c::Z3_context,d::Z3_fixedpoint,f::Z3_func_decl)
    ccall((:Z3_fixedpoint_register_relation,testclang),Void,(Z3_context,Z3_fixedpoint,Z3_func_decl),c,d,f)
end

function Z3_fixedpoint_set_predicate_representation(c::Z3_context,d::Z3_fixedpoint,f::Z3_func_decl,num_relations::Uint32,relation_kinds::Ptr{Z3_symbol})
    ccall((:Z3_fixedpoint_set_predicate_representation,testclang),Void,(Z3_context,Z3_fixedpoint,Z3_func_decl,Uint32,Ptr{Z3_symbol}),c,d,f,num_relations,relation_kinds)
end

function Z3_fixedpoint_get_rules(c::Z3_context,f::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_rules,testclang),Z3_ast_vector,(Z3_context,Z3_fixedpoint),c,f)
end

function Z3_fixedpoint_get_assertions(c::Z3_context,f::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_assertions,testclang),Z3_ast_vector,(Z3_context,Z3_fixedpoint),c,f)
end

function Z3_fixedpoint_set_params(c::Z3_context,f::Z3_fixedpoint,p::Z3_params)
    ccall((:Z3_fixedpoint_set_params,testclang),Void,(Z3_context,Z3_fixedpoint,Z3_params),c,f,p)
end

function Z3_fixedpoint_get_help(c::Z3_context,f::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_help,testclang),Z3_string,(Z3_context,Z3_fixedpoint),c,f)
end

function Z3_fixedpoint_get_param_descrs(c::Z3_context,f::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_get_param_descrs,testclang),Z3_param_descrs,(Z3_context,Z3_fixedpoint),c,f)
end

function Z3_fixedpoint_to_string(c::Z3_context,f::Z3_fixedpoint,num_queries::Uint32,queries::Ptr{Z3_ast})
    ccall((:Z3_fixedpoint_to_string,testclang),Z3_string,(Z3_context,Z3_fixedpoint,Uint32,Ptr{Z3_ast}),c,f,num_queries,queries)
end

function Z3_fixedpoint_from_string(c::Z3_context,f::Z3_fixedpoint,s::Z3_string)
    ccall((:Z3_fixedpoint_from_string,testclang),Z3_ast_vector,(Z3_context,Z3_fixedpoint,Z3_string),c,f,s)
end

function Z3_fixedpoint_from_file(c::Z3_context,f::Z3_fixedpoint,s::Z3_string)
    ccall((:Z3_fixedpoint_from_file,testclang),Z3_ast_vector,(Z3_context,Z3_fixedpoint,Z3_string),c,f,s)
end

function Z3_fixedpoint_push(c::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_push,testclang),Void,(Z3_context,Z3_fixedpoint),c,d)
end

function Z3_fixedpoint_pop(c::Z3_context,d::Z3_fixedpoint)
    ccall((:Z3_fixedpoint_pop,testclang),Void,(Z3_context,Z3_fixedpoint),c,d)
end

function Z3_fixedpoint_init(c::Z3_context,d::Z3_fixedpoint,state::Ptr{Void})
    ccall((:Z3_fixedpoint_init,testclang),Void,(Z3_context,Z3_fixedpoint,Ptr{Void}),c,d,state)
end

function Z3_fixedpoint_set_reduce_assign_callback(c::Z3_context,d::Z3_fixedpoint,cb::Z3_fixedpoint_reduce_assign_callback_fptr)
    ccall((:Z3_fixedpoint_set_reduce_assign_callback,testclang),Void,(Z3_context,Z3_fixedpoint,Z3_fixedpoint_reduce_assign_callback_fptr),c,d,cb)
end

function Z3_fixedpoint_set_reduce_app_callback(c::Z3_context,d::Z3_fixedpoint,cb::Z3_fixedpoint_reduce_app_callback_fptr)
    ccall((:Z3_fixedpoint_set_reduce_app_callback,testclang),Void,(Z3_context,Z3_fixedpoint,Z3_fixedpoint_reduce_app_callback_fptr),c,d,cb)
end

function Z3_mk_ast_vector(c::Z3_context)
    ccall((:Z3_mk_ast_vector,testclang),Z3_ast_vector,(Z3_context,),c)
end

function Z3_ast_vector_inc_ref(c::Z3_context,v::Z3_ast_vector)
    ccall((:Z3_ast_vector_inc_ref,testclang),Void,(Z3_context,Z3_ast_vector),c,v)
end

function Z3_ast_vector_dec_ref(c::Z3_context,v::Z3_ast_vector)
    ccall((:Z3_ast_vector_dec_ref,testclang),Void,(Z3_context,Z3_ast_vector),c,v)
end

function Z3_ast_vector_size(c::Z3_context,v::Z3_ast_vector)
    ccall((:Z3_ast_vector_size,testclang),Uint32,(Z3_context,Z3_ast_vector),c,v)
end

function Z3_ast_vector_get(c::Z3_context,v::Z3_ast_vector,i::Uint32)
    ccall((:Z3_ast_vector_get,testclang),Z3_ast,(Z3_context,Z3_ast_vector,Uint32),c,v,i)
end

function Z3_ast_vector_set(c::Z3_context,v::Z3_ast_vector,i::Uint32,a::Z3_ast)
    ccall((:Z3_ast_vector_set,testclang),Void,(Z3_context,Z3_ast_vector,Uint32,Z3_ast),c,v,i,a)
end

function Z3_ast_vector_resize(c::Z3_context,v::Z3_ast_vector,n::Uint32)
    ccall((:Z3_ast_vector_resize,testclang),Void,(Z3_context,Z3_ast_vector,Uint32),c,v,n)
end

function Z3_ast_vector_push(c::Z3_context,v::Z3_ast_vector,a::Z3_ast)
    ccall((:Z3_ast_vector_push,testclang),Void,(Z3_context,Z3_ast_vector,Z3_ast),c,v,a)
end

function Z3_ast_vector_translate(s::Z3_context,v::Z3_ast_vector,t::Z3_context)
    ccall((:Z3_ast_vector_translate,testclang),Z3_ast_vector,(Z3_context,Z3_ast_vector,Z3_context),s,v,t)
end

function Z3_ast_vector_to_string(c::Z3_context,v::Z3_ast_vector)
    ccall((:Z3_ast_vector_to_string,testclang),Z3_string,(Z3_context,Z3_ast_vector),c,v)
end

function Z3_mk_ast_map(c::Z3_context)
    ccall((:Z3_mk_ast_map,testclang),Z3_ast_map,(Z3_context,),c)
end

function Z3_ast_map_inc_ref(c::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_inc_ref,testclang),Void,(Z3_context,Z3_ast_map),c,m)
end

function Z3_ast_map_dec_ref(c::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_dec_ref,testclang),Void,(Z3_context,Z3_ast_map),c,m)
end

function Z3_ast_map_contains(c::Z3_context,m::Z3_ast_map,k::Z3_ast)
    ccall((:Z3_ast_map_contains,testclang),Z3_bool,(Z3_context,Z3_ast_map,Z3_ast),c,m,k)
end

function Z3_ast_map_find(c::Z3_context,m::Z3_ast_map,k::Z3_ast)
    ccall((:Z3_ast_map_find,testclang),Z3_ast,(Z3_context,Z3_ast_map,Z3_ast),c,m,k)
end

function Z3_ast_map_insert(c::Z3_context,m::Z3_ast_map,k::Z3_ast,v::Z3_ast)
    ccall((:Z3_ast_map_insert,testclang),Void,(Z3_context,Z3_ast_map,Z3_ast,Z3_ast),c,m,k,v)
end

function Z3_ast_map_erase(c::Z3_context,m::Z3_ast_map,k::Z3_ast)
    ccall((:Z3_ast_map_erase,testclang),Void,(Z3_context,Z3_ast_map,Z3_ast),c,m,k)
end

function Z3_ast_map_reset(c::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_reset,testclang),Void,(Z3_context,Z3_ast_map),c,m)
end

function Z3_ast_map_size(c::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_size,testclang),Uint32,(Z3_context,Z3_ast_map),c,m)
end

function Z3_ast_map_keys(c::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_keys,testclang),Z3_ast_vector,(Z3_context,Z3_ast_map),c,m)
end

function Z3_ast_map_to_string(c::Z3_context,m::Z3_ast_map)
    ccall((:Z3_ast_map_to_string,testclang),Z3_string,(Z3_context,Z3_ast_map),c,m)
end

function Z3_mk_goal(c::Z3_context,models::Z3_bool,unsat_cores::Z3_bool,proofs::Z3_bool)
    ccall((:Z3_mk_goal,testclang),Z3_goal,(Z3_context,Z3_bool,Z3_bool,Z3_bool),c,models,unsat_cores,proofs)
end

function Z3_goal_inc_ref(c::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_inc_ref,testclang),Void,(Z3_context,Z3_goal),c,g)
end

function Z3_goal_dec_ref(c::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_dec_ref,testclang),Void,(Z3_context,Z3_goal),c,g)
end

function Z3_goal_precision(c::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_precision,testclang),Z3_goal_prec,(Z3_context,Z3_goal),c,g)
end

function Z3_goal_assert(c::Z3_context,g::Z3_goal,a::Z3_ast)
    ccall((:Z3_goal_assert,testclang),Void,(Z3_context,Z3_goal,Z3_ast),c,g,a)
end

function Z3_goal_inconsistent(c::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_inconsistent,testclang),Z3_bool,(Z3_context,Z3_goal),c,g)
end

function Z3_goal_depth(c::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_depth,testclang),Uint32,(Z3_context,Z3_goal),c,g)
end

function Z3_goal_reset(c::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_reset,testclang),Void,(Z3_context,Z3_goal),c,g)
end

function Z3_goal_size(c::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_size,testclang),Uint32,(Z3_context,Z3_goal),c,g)
end

function Z3_goal_formula(c::Z3_context,g::Z3_goal,idx::Uint32)
    ccall((:Z3_goal_formula,testclang),Z3_ast,(Z3_context,Z3_goal,Uint32),c,g,idx)
end

function Z3_goal_num_exprs(c::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_num_exprs,testclang),Uint32,(Z3_context,Z3_goal),c,g)
end

function Z3_goal_is_decided_sat(c::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_is_decided_sat,testclang),Z3_bool,(Z3_context,Z3_goal),c,g)
end

function Z3_goal_is_decided_unsat(c::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_is_decided_unsat,testclang),Z3_bool,(Z3_context,Z3_goal),c,g)
end

function Z3_goal_translate(source::Z3_context,g::Z3_goal,target::Z3_context)
    ccall((:Z3_goal_translate,testclang),Z3_goal,(Z3_context,Z3_goal,Z3_context),source,g,target)
end

function Z3_goal_to_string(c::Z3_context,g::Z3_goal)
    ccall((:Z3_goal_to_string,testclang),Z3_string,(Z3_context,Z3_goal),c,g)
end

function Z3_mk_tactic(c::Z3_context,name::Z3_string)
    ccall((:Z3_mk_tactic,testclang),Z3_tactic,(Z3_context,Z3_string),c,name)
end

function Z3_tactic_inc_ref(c::Z3_context,t::Z3_tactic)
    ccall((:Z3_tactic_inc_ref,testclang),Void,(Z3_context,Z3_tactic),c,t)
end

function Z3_tactic_dec_ref(c::Z3_context,g::Z3_tactic)
    ccall((:Z3_tactic_dec_ref,testclang),Void,(Z3_context,Z3_tactic),c,g)
end

function Z3_mk_probe(c::Z3_context,name::Z3_string)
    ccall((:Z3_mk_probe,testclang),Z3_probe,(Z3_context,Z3_string),c,name)
end

function Z3_probe_inc_ref(c::Z3_context,p::Z3_probe)
    ccall((:Z3_probe_inc_ref,testclang),Void,(Z3_context,Z3_probe),c,p)
end

function Z3_probe_dec_ref(c::Z3_context,p::Z3_probe)
    ccall((:Z3_probe_dec_ref,testclang),Void,(Z3_context,Z3_probe),c,p)
end

function Z3_tactic_and_then(c::Z3_context,t1::Z3_tactic,t2::Z3_tactic)
    ccall((:Z3_tactic_and_then,testclang),Z3_tactic,(Z3_context,Z3_tactic,Z3_tactic),c,t1,t2)
end

function Z3_tactic_or_else(c::Z3_context,t1::Z3_tactic,t2::Z3_tactic)
    ccall((:Z3_tactic_or_else,testclang),Z3_tactic,(Z3_context,Z3_tactic,Z3_tactic),c,t1,t2)
end

function Z3_tactic_par_or(c::Z3_context,num::Uint32,ts::Ptr{Z3_tactic})
    ccall((:Z3_tactic_par_or,testclang),Z3_tactic,(Z3_context,Uint32,Ptr{Z3_tactic}),c,num,ts)
end

function Z3_tactic_par_and_then(c::Z3_context,t1::Z3_tactic,t2::Z3_tactic)
    ccall((:Z3_tactic_par_and_then,testclang),Z3_tactic,(Z3_context,Z3_tactic,Z3_tactic),c,t1,t2)
end

function Z3_tactic_try_for(c::Z3_context,t::Z3_tactic,ms::Uint32)
    ccall((:Z3_tactic_try_for,testclang),Z3_tactic,(Z3_context,Z3_tactic,Uint32),c,t,ms)
end

function Z3_tactic_when(c::Z3_context,p::Z3_probe,t::Z3_tactic)
    ccall((:Z3_tactic_when,testclang),Z3_tactic,(Z3_context,Z3_probe,Z3_tactic),c,p,t)
end

function Z3_tactic_cond(c::Z3_context,p::Z3_probe,t1::Z3_tactic,t2::Z3_tactic)
    ccall((:Z3_tactic_cond,testclang),Z3_tactic,(Z3_context,Z3_probe,Z3_tactic,Z3_tactic),c,p,t1,t2)
end

function Z3_tactic_repeat(c::Z3_context,t::Z3_tactic,max::Uint32)
    ccall((:Z3_tactic_repeat,testclang),Z3_tactic,(Z3_context,Z3_tactic,Uint32),c,t,max)
end

function Z3_tactic_skip(c::Z3_context)
    ccall((:Z3_tactic_skip,testclang),Z3_tactic,(Z3_context,),c)
end

function Z3_tactic_fail(c::Z3_context)
    ccall((:Z3_tactic_fail,testclang),Z3_tactic,(Z3_context,),c)
end

function Z3_tactic_fail_if(c::Z3_context,p::Z3_probe)
    ccall((:Z3_tactic_fail_if,testclang),Z3_tactic,(Z3_context,Z3_probe),c,p)
end

function Z3_tactic_fail_if_not_decided(c::Z3_context)
    ccall((:Z3_tactic_fail_if_not_decided,testclang),Z3_tactic,(Z3_context,),c)
end

function Z3_tactic_using_params(c::Z3_context,t::Z3_tactic,p::Z3_params)
    ccall((:Z3_tactic_using_params,testclang),Z3_tactic,(Z3_context,Z3_tactic,Z3_params),c,t,p)
end

function Z3_probe_const(x::Z3_context,val::Cdouble)
    ccall((:Z3_probe_const,testclang),Z3_probe,(Z3_context,Cdouble),x,val)
end

function Z3_probe_lt(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_lt,testclang),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

function Z3_probe_gt(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_gt,testclang),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

function Z3_probe_le(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_le,testclang),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

function Z3_probe_ge(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_ge,testclang),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

function Z3_probe_eq(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_eq,testclang),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

function Z3_probe_and(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_and,testclang),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

function Z3_probe_or(x::Z3_context,p1::Z3_probe,p2::Z3_probe)
    ccall((:Z3_probe_or,testclang),Z3_probe,(Z3_context,Z3_probe,Z3_probe),x,p1,p2)
end

function Z3_probe_not(x::Z3_context,p::Z3_probe)
    ccall((:Z3_probe_not,testclang),Z3_probe,(Z3_context,Z3_probe),x,p)
end

function Z3_get_num_tactics(c::Z3_context)
    ccall((:Z3_get_num_tactics,testclang),Uint32,(Z3_context,),c)
end

function Z3_get_tactic_name(c::Z3_context,i::Uint32)
    ccall((:Z3_get_tactic_name,testclang),Z3_string,(Z3_context,Uint32),c,i)
end

function Z3_get_num_probes(c::Z3_context)
    ccall((:Z3_get_num_probes,testclang),Uint32,(Z3_context,),c)
end

function Z3_get_probe_name(c::Z3_context,i::Uint32)
    ccall((:Z3_get_probe_name,testclang),Z3_string,(Z3_context,Uint32),c,i)
end

function Z3_tactic_get_help(c::Z3_context,t::Z3_tactic)
    ccall((:Z3_tactic_get_help,testclang),Z3_string,(Z3_context,Z3_tactic),c,t)
end

function Z3_tactic_get_param_descrs(c::Z3_context,t::Z3_tactic)
    ccall((:Z3_tactic_get_param_descrs,testclang),Z3_param_descrs,(Z3_context,Z3_tactic),c,t)
end

function Z3_tactic_get_descr(c::Z3_context,name::Z3_string)
    ccall((:Z3_tactic_get_descr,testclang),Z3_string,(Z3_context,Z3_string),c,name)
end

function Z3_probe_get_descr(c::Z3_context,name::Z3_string)
    ccall((:Z3_probe_get_descr,testclang),Z3_string,(Z3_context,Z3_string),c,name)
end

function Z3_probe_apply(c::Z3_context,p::Z3_probe,g::Z3_goal)
    ccall((:Z3_probe_apply,testclang),Cdouble,(Z3_context,Z3_probe,Z3_goal),c,p,g)
end

function Z3_tactic_apply(c::Z3_context,t::Z3_tactic,g::Z3_goal)
    ccall((:Z3_tactic_apply,testclang),Z3_apply_result,(Z3_context,Z3_tactic,Z3_goal),c,t,g)
end

function Z3_tactic_apply_ex(c::Z3_context,t::Z3_tactic,g::Z3_goal,p::Z3_params)
    ccall((:Z3_tactic_apply_ex,testclang),Z3_apply_result,(Z3_context,Z3_tactic,Z3_goal,Z3_params),c,t,g,p)
end

function Z3_apply_result_inc_ref(c::Z3_context,r::Z3_apply_result)
    ccall((:Z3_apply_result_inc_ref,testclang),Void,(Z3_context,Z3_apply_result),c,r)
end

function Z3_apply_result_dec_ref(c::Z3_context,r::Z3_apply_result)
    ccall((:Z3_apply_result_dec_ref,testclang),Void,(Z3_context,Z3_apply_result),c,r)
end

function Z3_apply_result_to_string(c::Z3_context,r::Z3_apply_result)
    ccall((:Z3_apply_result_to_string,testclang),Z3_string,(Z3_context,Z3_apply_result),c,r)
end

function Z3_apply_result_get_num_subgoals(c::Z3_context,r::Z3_apply_result)
    ccall((:Z3_apply_result_get_num_subgoals,testclang),Uint32,(Z3_context,Z3_apply_result),c,r)
end

function Z3_apply_result_get_subgoal(c::Z3_context,r::Z3_apply_result,i::Uint32)
    ccall((:Z3_apply_result_get_subgoal,testclang),Z3_goal,(Z3_context,Z3_apply_result,Uint32),c,r,i)
end

function Z3_apply_result_convert_model(c::Z3_context,r::Z3_apply_result,i::Uint32,m::Z3_model)
    ccall((:Z3_apply_result_convert_model,testclang),Z3_model,(Z3_context,Z3_apply_result,Uint32,Z3_model),c,r,i,m)
end

function Z3_mk_solver(c::Z3_context)
    ccall((:Z3_mk_solver,testclang),Z3_solver,(Z3_context,),c)
end

function Z3_mk_simple_solver(c::Z3_context)
    ccall((:Z3_mk_simple_solver,testclang),Z3_solver,(Z3_context,),c)
end

function Z3_mk_solver_for_logic(c::Z3_context,logic::Z3_symbol)
    ccall((:Z3_mk_solver_for_logic,testclang),Z3_solver,(Z3_context,Z3_symbol),c,logic)
end

function Z3_mk_solver_from_tactic(c::Z3_context,t::Z3_tactic)
    ccall((:Z3_mk_solver_from_tactic,testclang),Z3_solver,(Z3_context,Z3_tactic),c,t)
end

function Z3_solver_get_help(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_help,testclang),Z3_string,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_get_param_descrs(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_param_descrs,testclang),Z3_param_descrs,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_set_params(c::Z3_context,s::Z3_solver,p::Z3_params)
    ccall((:Z3_solver_set_params,testclang),Void,(Z3_context,Z3_solver,Z3_params),c,s,p)
end

function Z3_solver_inc_ref(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_inc_ref,testclang),Void,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_dec_ref(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_dec_ref,testclang),Void,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_push(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_push,testclang),Void,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_pop(c::Z3_context,s::Z3_solver,n::Uint32)
    ccall((:Z3_solver_pop,testclang),Void,(Z3_context,Z3_solver,Uint32),c,s,n)
end

function Z3_solver_reset(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_reset,testclang),Void,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_get_num_scopes(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_num_scopes,testclang),Uint32,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_assert(c::Z3_context,s::Z3_solver,a::Z3_ast)
    ccall((:Z3_solver_assert,testclang),Void,(Z3_context,Z3_solver,Z3_ast),c,s,a)
end

function Z3_solver_assert_and_track(c::Z3_context,s::Z3_solver,a::Z3_ast,p::Z3_ast)
    ccall((:Z3_solver_assert_and_track,testclang),Void,(Z3_context,Z3_solver,Z3_ast,Z3_ast),c,s,a,p)
end

function Z3_solver_get_assertions(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_assertions,testclang),Z3_ast_vector,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_check(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_check,testclang),Z3_lbool,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_check_assumptions(c::Z3_context,s::Z3_solver,num_assumptions::Uint32,assumptions::Ptr{Z3_ast})
    ccall((:Z3_solver_check_assumptions,testclang),Z3_lbool,(Z3_context,Z3_solver,Uint32,Ptr{Z3_ast}),c,s,num_assumptions,assumptions)
end

function Z3_solver_get_model(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_model,testclang),Z3_model,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_get_proof(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_proof,testclang),Z3_ast,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_get_unsat_core(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_unsat_core,testclang),Z3_ast_vector,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_get_reason_unknown(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_reason_unknown,testclang),Z3_string,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_get_statistics(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_get_statistics,testclang),Z3_stats,(Z3_context,Z3_solver),c,s)
end

function Z3_solver_to_string(c::Z3_context,s::Z3_solver)
    ccall((:Z3_solver_to_string,testclang),Z3_string,(Z3_context,Z3_solver),c,s)
end

function Z3_stats_to_string(c::Z3_context,s::Z3_stats)
    ccall((:Z3_stats_to_string,testclang),Z3_string,(Z3_context,Z3_stats),c,s)
end

function Z3_stats_inc_ref(c::Z3_context,s::Z3_stats)
    ccall((:Z3_stats_inc_ref,testclang),Void,(Z3_context,Z3_stats),c,s)
end

function Z3_stats_dec_ref(c::Z3_context,s::Z3_stats)
    ccall((:Z3_stats_dec_ref,testclang),Void,(Z3_context,Z3_stats),c,s)
end

function Z3_stats_size(c::Z3_context,s::Z3_stats)
    ccall((:Z3_stats_size,testclang),Uint32,(Z3_context,Z3_stats),c,s)
end

function Z3_stats_get_key(c::Z3_context,s::Z3_stats,idx::Uint32)
    ccall((:Z3_stats_get_key,testclang),Z3_string,(Z3_context,Z3_stats,Uint32),c,s,idx)
end

function Z3_stats_is_uint(c::Z3_context,s::Z3_stats,idx::Uint32)
    ccall((:Z3_stats_is_uint,testclang),Z3_bool,(Z3_context,Z3_stats,Uint32),c,s,idx)
end

function Z3_stats_is_double(c::Z3_context,s::Z3_stats,idx::Uint32)
    ccall((:Z3_stats_is_double,testclang),Z3_bool,(Z3_context,Z3_stats,Uint32),c,s,idx)
end

function Z3_stats_get_uint_value(c::Z3_context,s::Z3_stats,idx::Uint32)
    ccall((:Z3_stats_get_uint_value,testclang),Uint32,(Z3_context,Z3_stats,Uint32),c,s,idx)
end

function Z3_stats_get_double_value(c::Z3_context,s::Z3_stats,idx::Uint32)
    ccall((:Z3_stats_get_double_value,testclang),Cdouble,(Z3_context,Z3_stats,Uint32),c,s,idx)
end

function Z3_mk_injective_function(c::Z3_context,s::Z3_symbol,domain_size::Uint32,domain::Ptr{Z3_sort},range::Z3_sort)
    ccall((:Z3_mk_injective_function,testclang),Z3_func_decl,(Z3_context,Z3_symbol,Uint32,Ptr{Z3_sort},Z3_sort),c,s,domain_size,domain,range)
end

function Z3_set_logic(c::Z3_context,logic::Z3_string)
    ccall((:Z3_set_logic,testclang),Z3_bool,(Z3_context,Z3_string),c,logic)
end

function Z3_push(c::Z3_context)
    ccall((:Z3_push,testclang),Void,(Z3_context,),c)
end

function Z3_pop(c::Z3_context,num_scopes::Uint32)
    ccall((:Z3_pop,testclang),Void,(Z3_context,Uint32),c,num_scopes)
end

function Z3_get_num_scopes(c::Z3_context)
    ccall((:Z3_get_num_scopes,testclang),Uint32,(Z3_context,),c)
end

function Z3_persist_ast(c::Z3_context,a::Z3_ast,num_scopes::Uint32)
    ccall((:Z3_persist_ast,testclang),Void,(Z3_context,Z3_ast,Uint32),c,a,num_scopes)
end

function Z3_assert_cnstr(c::Z3_context,a::Z3_ast)
    ccall((:Z3_assert_cnstr,testclang),Void,(Z3_context,Z3_ast),c,a)
end

function Z3_check_and_get_model(c::Z3_context,m::Ptr{Z3_model})
    ccall((:Z3_check_and_get_model,testclang),Z3_lbool,(Z3_context,Ptr{Z3_model}),c,m)
end

function Z3_check(c::Z3_context)
    ccall((:Z3_check,testclang),Z3_lbool,(Z3_context,),c)
end

function Z3_check_assumptions(c::Z3_context,num_assumptions::Uint32,assumptions::Ptr{Z3_ast},m::Ptr{Z3_model},proof::Ptr{Z3_ast},core_size::Ptr{Uint32},core::Ptr{Z3_ast})
    ccall((:Z3_check_assumptions,testclang),Z3_lbool,(Z3_context,Uint32,Ptr{Z3_ast},Ptr{Z3_model},Ptr{Z3_ast},Ptr{Uint32},Ptr{Z3_ast}),c,num_assumptions,assumptions,m,proof,core_size,core)
end

function Z3_get_implied_equalities(c::Z3_context,s::Z3_solver,num_terms::Uint32,terms::Ptr{Z3_ast},class_ids::Ptr{Uint32})
    ccall((:Z3_get_implied_equalities,testclang),Z3_lbool,(Z3_context,Z3_solver,Uint32,Ptr{Z3_ast},Ptr{Uint32}),c,s,num_terms,terms,class_ids)
end

function Z3_del_model(c::Z3_context,m::Z3_model)
    ccall((:Z3_del_model,testclang),Void,(Z3_context,Z3_model),c,m)
end

function Z3_soft_check_cancel(c::Z3_context)
    ccall((:Z3_soft_check_cancel,testclang),Void,(Z3_context,),c)
end

function Z3_get_search_failure(c::Z3_context)
    ccall((:Z3_get_search_failure,testclang),Z3_search_failure,(Z3_context,),c)
end

function Z3_mk_label(c::Z3_context,s::Z3_symbol,is_pos::Z3_bool,f::Z3_ast)
    ccall((:Z3_mk_label,testclang),Z3_ast,(Z3_context,Z3_symbol,Z3_bool,Z3_ast),c,s,is_pos,f)
end

function Z3_get_relevant_labels(c::Z3_context)
    ccall((:Z3_get_relevant_labels,testclang),Z3_literals,(Z3_context,),c)
end

function Z3_get_relevant_literals(c::Z3_context)
    ccall((:Z3_get_relevant_literals,testclang),Z3_literals,(Z3_context,),c)
end

function Z3_get_guessed_literals(c::Z3_context)
    ccall((:Z3_get_guessed_literals,testclang),Z3_literals,(Z3_context,),c)
end

function Z3_del_literals(c::Z3_context,lbls::Z3_literals)
    ccall((:Z3_del_literals,testclang),Void,(Z3_context,Z3_literals),c,lbls)
end

function Z3_get_num_literals(c::Z3_context,lbls::Z3_literals)
    ccall((:Z3_get_num_literals,testclang),Uint32,(Z3_context,Z3_literals),c,lbls)
end

function Z3_get_label_symbol(c::Z3_context,lbls::Z3_literals,idx::Uint32)
    ccall((:Z3_get_label_symbol,testclang),Z3_symbol,(Z3_context,Z3_literals,Uint32),c,lbls,idx)
end

function Z3_get_literal(c::Z3_context,lbls::Z3_literals,idx::Uint32)
    ccall((:Z3_get_literal,testclang),Z3_ast,(Z3_context,Z3_literals,Uint32),c,lbls,idx)
end

function Z3_disable_literal(c::Z3_context,lbls::Z3_literals,idx::Uint32)
    ccall((:Z3_disable_literal,testclang),Void,(Z3_context,Z3_literals,Uint32),c,lbls,idx)
end

function Z3_block_literals(c::Z3_context,lbls::Z3_literals)
    ccall((:Z3_block_literals,testclang),Void,(Z3_context,Z3_literals),c,lbls)
end

function Z3_get_model_num_constants(c::Z3_context,m::Z3_model)
    ccall((:Z3_get_model_num_constants,testclang),Uint32,(Z3_context,Z3_model),c,m)
end

function Z3_get_model_constant(c::Z3_context,m::Z3_model,i::Uint32)
    ccall((:Z3_get_model_constant,testclang),Z3_func_decl,(Z3_context,Z3_model,Uint32),c,m,i)
end

function Z3_get_model_num_funcs(c::Z3_context,m::Z3_model)
    ccall((:Z3_get_model_num_funcs,testclang),Uint32,(Z3_context,Z3_model),c,m)
end

function Z3_get_model_func_decl(c::Z3_context,m::Z3_model,i::Uint32)
    ccall((:Z3_get_model_func_decl,testclang),Z3_func_decl,(Z3_context,Z3_model,Uint32),c,m,i)
end

function Z3_eval_func_decl(c::Z3_context,m::Z3_model,decl::Z3_func_decl,v::Ptr{Z3_ast})
    ccall((:Z3_eval_func_decl,testclang),Z3_bool,(Z3_context,Z3_model,Z3_func_decl,Ptr{Z3_ast}),c,m,decl,v)
end

function Z3_is_array_value(c::Z3_context,m::Z3_model,v::Z3_ast,num_entries::Ptr{Uint32})
    ccall((:Z3_is_array_value,testclang),Z3_bool,(Z3_context,Z3_model,Z3_ast,Ptr{Uint32}),c,m,v,num_entries)
end

function Z3_get_array_value(c::Z3_context,m::Z3_model,v::Z3_ast,num_entries::Uint32,indices::Ptr{Z3_ast},values::Ptr{Z3_ast},else_value::Ptr{Z3_ast})
    ccall((:Z3_get_array_value,testclang),Void,(Z3_context,Z3_model,Z3_ast,Uint32,Ptr{Z3_ast},Ptr{Z3_ast},Ptr{Z3_ast}),c,m,v,num_entries,indices,values,else_value)
end

function Z3_get_model_func_else(c::Z3_context,m::Z3_model,i::Uint32)
    ccall((:Z3_get_model_func_else,testclang),Z3_ast,(Z3_context,Z3_model,Uint32),c,m,i)
end

function Z3_get_model_func_num_entries(c::Z3_context,m::Z3_model,i::Uint32)
    ccall((:Z3_get_model_func_num_entries,testclang),Uint32,(Z3_context,Z3_model,Uint32),c,m,i)
end

function Z3_get_model_func_entry_num_args(c::Z3_context,m::Z3_model,i::Uint32,j::Uint32)
    ccall((:Z3_get_model_func_entry_num_args,testclang),Uint32,(Z3_context,Z3_model,Uint32,Uint32),c,m,i,j)
end

function Z3_get_model_func_entry_arg(c::Z3_context,m::Z3_model,i::Uint32,j::Uint32,k::Uint32)
    ccall((:Z3_get_model_func_entry_arg,testclang),Z3_ast,(Z3_context,Z3_model,Uint32,Uint32,Uint32),c,m,i,j,k)
end

function Z3_get_model_func_entry_value(c::Z3_context,m::Z3_model,i::Uint32,j::Uint32)
    ccall((:Z3_get_model_func_entry_value,testclang),Z3_ast,(Z3_context,Z3_model,Uint32,Uint32),c,m,i,j)
end

function Z3_eval(c::Z3_context,m::Z3_model,t::Z3_ast,v::Ptr{Z3_ast})
    ccall((:Z3_eval,testclang),Z3_bool,(Z3_context,Z3_model,Z3_ast,Ptr{Z3_ast}),c,m,t,v)
end

function Z3_eval_decl(c::Z3_context,m::Z3_model,d::Z3_func_decl,num_args::Uint32,args::Ptr{Z3_ast},v::Ptr{Z3_ast})
    ccall((:Z3_eval_decl,testclang),Z3_bool,(Z3_context,Z3_model,Z3_func_decl,Uint32,Ptr{Z3_ast},Ptr{Z3_ast}),c,m,d,num_args,args,v)
end

function Z3_context_to_string(c::Z3_context)
    ccall((:Z3_context_to_string,testclang),Z3_string,(Z3_context,),c)
end

function Z3_statistics_to_string(c::Z3_context)
    ccall((:Z3_statistics_to_string,testclang),Z3_string,(Z3_context,),c)
end

function Z3_get_context_assignment(c::Z3_context)
    ccall((:Z3_get_context_assignment,testclang),Z3_ast,(Z3_context,),c)
end
