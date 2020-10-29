import analysis.locally_convex_space.basic

namespace convenient

  local notation ` ∞ ` := ⊤
  local notation ` ℕ* ` := with_top ℕ

  --   ___
  --  / __|  _ _ ___ _____
  -- | (_| || | '_\ V / -_)
  --  \___\_,_|_|  \_/\___|
  @[reducible, inline] def curve (E : Type*) 
    [add_comm_group E] [vector_space ℝ E] 
    [topological_space E] [locally_convex_space ℝ E] := ℝ → E
  
  namespace curve
    variables {E : Type*}
    variables [add_comm_group E] [vector_space ℝ E] 
    variables [topological_space E] [locally_convex_space ℝ E]   
    
    def is_deriv_at (c : curve E) (c' : E) (t : ℝ) : Prop := 
      filter.tendsto (λ h, (1/h) • (c (t + h) - c(t))) (nhds 0) (nhds c')
    
    def is_deriv (c c': curve E) : Prop :=  ∀ t, c.is_deriv_at (c' t) t

    /- maybe define nsmooth with enat instead of nat, but enat has some fucked up definition. -/
    /- Why is enat just simply defined as ℕ⊕unit -/
    def is_nsmooth' : ℕ → curve E → Prop
    | 0 c := continuous c
    | (n+1) c := ∃ (c' : curve E), (is_deriv c c') ∧ (is_nsmooth' n c')

    def is_nsmooth : ℕ* → curve E → Prop
    | (some n) c := is_nsmooth' n c
    | none c := ∀ n : ℕ, is_nsmooth' n c

    def is_smooth (c : curve E) : Prop := is_nsmooth ∞ c

    class has_explicit_anti_derivative (c' : curve E) := 
      (c : curve E)
      (zero_at_zero : c 0 = 0)
      (is_anti_derivative : is_deriv c c')
  
    lemma zero.is_nsmooth (n : ℕ*) : is_nsmooth n (0 : curve E) := sorry

    lemma add.is_nsmooth (n : ℕ*) (c d : curve E) : is_nsmooth n c → is_nsmooth n d → is_nsmooth n (c+d) :=
    begin
      sorry
    end 

    lemma smul.is_nsmooth (n : ℕ*) (s : ℝ) (c : curve E) : is_nsmooth n c → is_nsmooth n (s•c) :=
    begin
      sorry
    end 

  end curve 

  --  ___                _   _       ___
  -- / __|_ __  ___  ___| |_| |_    / __|  _ _ ___ _____
  -- \__ \ '  \/ _ \/ _ \  _| ' \  | (_| || | '_\ V / -_)
  -- |___/_|_|_\___/\___/\__|_||_|  \___\_,_|_|  \_/\___|

  /- TODO: It should not be a submodule! Submodule automatically generates a topology that is not the one we want to use -/
  def nsmooth_curve (n : ℕ*) (E : Type*) 
    [add_comm_group E] [vector_space ℝ E] 
    [topological_space E] [locally_convex_space ℝ E] := 
    submodule.mk (curve.is_nsmooth n : curve E → Prop) 
      (curve.zero.is_nsmooth n) 
      (curve.add.is_nsmooth n) 
      (curve.smul.is_nsmooth n)

  @[reducible] 
  def smooth_curve (E : Type*) 
    [add_comm_group E] [vector_space ℝ E] 
    [topological_space E] [locally_convex_space ℝ E] := nsmooth_curve ∞ E
  
  namespace smooth_curve
    variables {n : ℕ*} {E : Type*} 
    variables [add_comm_group E] [vector_space ℝ E] 
    variables [topological_space E] [locally_convex_space ℝ E]
    -- variables [locally_convex_space ℝ ℝ]

    instance : has_coe_to_fun (nsmooth_curve n E) := has_coe_to_fun.mk _ subtype.val

    def is_deriv (c c' : smooth_curve E) := curve.is_deriv c c'

    section this_should_be_done_differently
      lemma deriv_exists (c : smooth_curve E) : nonempty {c' : smooth_curve E | is_deriv c c'} := sorry
      lemma deriv_unique (c : smooth_curve E) (c'₁ c'₂) : is_deriv c c'₁ → is_deriv c c'₂ → c'₁ = c'₂ := sorry

      noncomputable def deriv (c : smooth_curve E) : smooth_curve E := (classical.choice (deriv_exists c)).val
      def deriv.proof (c : smooth_curve E) := (classical.choice (deriv_exists c)).property
    end this_should_be_done_differently

    noncomputable def nderiv : ℕ → smooth_curve E → smooth_curve E
    | 0 c := c
    | (n+1) c := deriv (nderiv n c)

    noncomputable def line (x v : E) : smooth_curve E := ⟨λ t, x + t • v, begin sorry  end⟩

    /- TODO: fix the problem with getting an instance of `locally_convex_space ℝ ℝ` -/
    -- def comp.is_smooth : ∀ {c : smooth_curve E} {d : smooth_curve ℝ}, curve.is_smooth (c ∘ d) := sorry
    -- noncomputable def comp (c : smooth_curve E) (d : smooth_curve ℝ) : smooth_curve E  := ⟨c ∘ d, comp.is_smooth⟩

    @[simp] lemma apply (c : smooth_curve E) (t : ℝ) : c t = c.val t :=
    begin
      unfold coe_fn, unfold has_coe_to_fun.coe,
    end

    lemma ext (c c' : smooth_curve E) : (∀ t, c t = c' t) → c = c' :=
    begin
      intros h, induction c, induction c', simp, apply funext, simp at h, apply h,
    end

    /- A single seminorm on (smooth_curve E) give a signle seminorm on E -/
    noncomputable def curve_seminorm (k : ℕ) (T : ℝ) (q : seminorm ℝ E) : seminorm ℝ (smooth_curve E) :=
      { to_fun := λ c, ⨅ s ∈ { t : ℝ | ∥t∥ ≤ T}, q (nderiv k c s),
        smul := sorry,
        triangle := sorry }

    /- produce family of seminorms on (smooth_curve E) given a family of seminorms on E -/
    noncomputable def curve_seminorm_family {ι : Type*} (sf : ι → seminorm ℝ E) : (ℕ×ℝ×ι) → seminorm ℝ (smooth_curve E) :=
      λ idx : ℕ×ℝ×ι, 
      let k := idx.1 in
      let T := idx.2.1 in
      let i := idx.2.2 in
      curve_seminorm k T (sf i)

    noncomputable instance : topological_space (smooth_curve E) := sorry /- construct the topology from the above seminorms -/

    instance : locally_convex_space ℝ (smooth_curve E) := sorry 

  end smooth_curve

end convenient

