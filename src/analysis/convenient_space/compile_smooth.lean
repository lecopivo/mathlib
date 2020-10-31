import analysis.convenient_space.combinators

noncomputable theory

namespace convenient

  open convenient.combinators.smooth

  namespace compile_smooth_detail

    meta def get_smooth_version (f : expr) : tactic expr :=
    do
     fmt ← tactic.pp f,
     type_fmt ← tactic.infer_type f >>= tactic.pp,
     inst ← (tactic.to_expr ``(has_smooth_version %%f) >>= tactic.mk_instance) <|>
           tactic.fail (fmt.to_string ++ " : " ++ type_fmt.to_string ++ " does not have a smooth version!"),
     -- f ← tactic.to_expr ``(@has_smooth_version.func _ _ _ _ _ _ _ %%inst),
     tactic.trace "hohooh",
     f ← tactic.to_expr ``(has_smooth_version.func %%f),
     f ← tactic.dunfold [``has_smooth_version.func] f,
     pure f

    meta def extract_smooth_local : expr → expr → tactic expr
    | a (expr.app f x) := 
    do
      A ← tactic.infer_type a,
      X ← tactic.infer_type x,
      Y ← (tactic.to_expr ```(%%(expr.app f x))) >>= tactic.infer_type,
      let hf := expr.occurs a f,
      let hx := expr.occurs a x,
      (match hf, hx with
        | ff, ff := do
          tactic.trace "00",
          tactic.trace f,
          tactic.trace x,
          tactic.trace a,
          (tactic.to_expr ```((K %%(expr.app f x)) : (%%A ⟿ %%Y)))
        | ff, tt := 
          do
          tactic.trace "01",
          tactic.trace f,
          tactic.trace x,
          tactic.trace a,
          f ← get_smooth_version f,
            if (x=ₐa) then
              pure f 
            else do
            x ← extract_smooth_local a x,
            tactic.to_expr ``(B %%f %%x)
        | tt, ff := do
          -- Here finding smooth version of f is not necessary
          tactic.trace "10",
          tactic.trace f,
          tactic.trace x,
          tactic.trace a,       
          f ← (get_smooth_version f) <|> tactic.fail ("We are unable to prove smoothness of " ++ f.to_string ++ ". In this case, the smoothness is not necessary, but currently `compile_smooth` is not powerfull enough to handle case when this function is not smooth. Either prove smoothness by providing instance of `has_smooth_version` or your are left alone and you have to create smooth version by hand."),
          f ← extract_smooth_local a f, 
          tactic.to_expr ``(C %%f %%x)
        | tt, tt := do
          tactic.trace "11",
          tactic.trace f,
          tactic.trace x,
          tactic.trace a,
          f ← get_smooth_version f,
          x ← extract_smooth_local a x,
          f ← extract_smooth_local a f,
          tactic.to_expr ``(S %%f %%x)
      end)
    | a (expr.lam var_name bi var_type body) := 
      let lvar := (expr.local_const var_name var_name binder_info.default var_type) in do
      body' ← extract_smooth_local lvar (body.instantiate_var lvar),
      (extract_smooth_local a body')
    | a  (expr.elet var_name var_type assignment body) := 
      let lvar := (expr.local_const var_name var_name binder_info.default var_type) in do
      body ← extract_smooth_local lvar (body.instantiate_var lvar),
      body ← tactic.to_expr ```(%%body %%assignment),
      (extract_smooth_local a body)
    | a x := 
      do
        A ← tactic.infer_type a,
        X ← tactic.infer_type x,
        if (x=ₐa) then do
          tactic.to_expr ``(I : (%%A ⟿ %%A))
        else
          tactic.to_expr ``(K %%x : %%A ⟿  %%X)

    meta def compile : expr → tactic expr
    | (expr.lam var_name bi var_type body) := 
      let lvar := (expr.local_const var_name var_name binder_info.default var_type) in do
      extract_smooth_local lvar (body.instantiate_var lvar)
    | e := tactic.fail "Not a lambda expression!"

  end compile_smooth_detail
  
  meta def compile_smooth (e : pexpr) : tactic unit := tactic.to_expr e >>= compile_smooth_detail.compile >>= tactic.exact

end convenient
