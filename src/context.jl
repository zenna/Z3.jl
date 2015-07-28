# """
# Enable model construction. Other configuration parameters can be passed in the cfg variable
# Also enable tracing to stderr and register custom error handler.
# """
# function mk_context_custom(cfg::Config, err::Z3_error_handler)
#   Z3_set_param_value(cfg, "model", "true");
#   ctx = Z3_mk_context(cfg);
#   Z3_set_error_handler(ctx, err);
#   ctx
# end

"""
Create a logical context.
Enable model construction only.
Also enable tracing to stderr and register standard error handler.
"""
function mk_context()
  cfg = mk_config()
  ctx = mk_context(cfg)
  del_config(cfg)
  ctx
end

"Create a context under a specified logic."
function mk_context(l::Logic)
  cfg = mk_config()
  ctx = mk_context(cfg)
  del_config(cfg)
  set_logic(ctx, string(l))
  ctx
end

"""
Create a logical context.

Enable fine-grained proof construction.
Enable model construction.

Also enable tracing to stderr and register standard error handler.
"""
function mk_proof_context()
  cfg = mk_config();
  set_param_value(cfg, "proof", "true");
  mk_context_custom(cfg, throw_z3_error);
  del_config(cfg);
  ctx
end

## Global Context - default context for conveniece
#3 ==============

Context(l::Logic) = mk_context(l)
Context() = mk_context()

create_global_ctx() =
  (global default_global_context; default_global_context = Context())
global_context() = (global default_global_context; default_global_context)

function set_global_ctx(ctx::Context)
  global default_global_context
  default_global_context = ctx
end

function reset_global_ctx()
  delete_ctx!(global_context())
  create_global_ctx!(l)
end
