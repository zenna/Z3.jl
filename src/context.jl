## Context
#3 =======

Context(l::Logic) = mk_context(l)
Context() = mk_context()

"Create a global context, used by default for conveience"
create_global_ctx() =
  (global default_global_ctx; default_global_ctx = Context())

"Return the global context, used by default for conveience"
function global_ctx()
  # error("global_ctx_disabled")
  (global default_global_ctx; default_global_ctx)
end

"Assign the global context to `ctx`"
function set_global_ctx!(ctx::Context)
  global default_global_ctx
  default_global_ctx = ctx
end

"Reset the global context"
function reset_global_ctx!()
  delete_ctx!(global_ctx())
  create_global_ctx!(l)
end

"Disable use of global ctx, useful for debugging"
function disable_global_ctx!()
  @eval global_ctx() =  error("global_ctx_disabled")
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
  cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "proof", "true");
  ctx = mk_context(cfg)
  Z3_del_config(cfg);
  ctx
end
