import analysis.convenient_space.smooth_map
import analysis.convenient_space.smooth_linear_map
import analysis.convenient_space.differential
import analysis.convenient_space.exponential

namespace convenient

  /- The namespace space smooth containes couple usefull smooth functions -/
  namespace smooth
    variables 
      {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E] [locally_convex_space ℝ E]
      {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F] [locally_convex_space ℝ F] 
      {G : Type*} [add_comm_group G] [vector_space ℝ G] [topological_space G] [locally_convex_space ℝ G] 
      {H : Type*} [add_comm_group H] [vector_space ℝ H] [topological_space H] [locally_convex_space ℝ H] 
    
    noncomputable def eval : (E⟿F)×E⟿F := id.uncurry 
    noncomputable def pair : E⟿F⟿E×F := id.curry
    noncomputable def comp : (F⟿G)⟿(E⟿F)⟿(E⟿G) := (eval.comp $ (id.pair_map eval).comp $ assocr).curry.curry
    noncomputable def curry : ((E×F)⟿G)⟿(E⟿F⟿G) := (eval.comp assocr).curry.curry
    noncomputable def uncurry : (E⟿F⟿G)⟿((E×F)⟿G) := (eval.comp $ (eval.pair_map id).comp $ assocl).curry

    /- hom bifunctor (f,g) → (h → g∘h∘f)) -/
    noncomputable def hom : (E⟿F)×(G⟿H)⟿((F⟿G)⟿(E⟿H)) := 
      (comp.uncurry.comp $ (id.pair_map comp.uncurry).comp $ assocr.comp $ perm.ba.comp $ assocr).curry
    
    /- product bifunctor -/
    noncomputable def pair_map : (E⟿F)⟿(G⟿H)⟿(E×G⟿F×H) := ((eval.pair_map eval).comp $ perm.ac_bd).curry.curry

    /- Normalization - prefer functions in `smooth.??` over `smooth_map.??` -/
    @[simp] lemma comp_coe : smooth_map.comp = (λ f, smooth.comp f : (F⟿G)→(E⟿F)→(E⟿G)) := rfl 
    @[simp] lemma curry_coe  : smooth_map.curry = (smooth.curry : ((E×F)⟿G)→(E⟿F⟿G)) := rfl
    @[simp] lemma uncurry_coe : smooth_map.uncurry = (smooth.uncurry : (E⟿F⟿G)→((E×F)⟿G)) := rfl
    @[simp] lemma pair_map_coe : smooth_map.pair_map = (λ f g, smooth.pair_map f g : (E⟿F)→(G⟿H)→(E×G⟿F×H)) := rfl

    variables (f : F⟿G) (g : E⟿F) (x : E) (y : F) (p : E×F)    
    @[simp] lemma eval_apply : eval (g,x) = g x := rfl 
    @[simp] lemma pair_apply : pair x y = (x,y) := rfl 
    @[simp] lemma comp_apply : comp f g x = f (g x) := rfl
    @[simp] lemma curry_apply (f : E×F⟿G) : curry f x y = f (x,y) := rfl
    @[simp] lemma uncurry_apply (f : E⟿F⟿G) : uncurry f p = f p.1 p.2 := rfl
    @[simp] lemma hom_apply (fg : (E⟿F)×(G⟿H)) (h : F⟿G) : hom fg h = comp fg.2 (comp h fg.1) := rfl
    @[simp] lemma pair_map_apply (f : E⟿F) (g : G⟿H) (p : E×G) : pair_map f g p = (f p.1, g p.2) := rfl

    noncomputable def const : E⟿F⟿E := curry fst
    noncomputable def swap_pair : (E×F⟿F×E) := (pair_map snd fst).comp diag
    @[reducible, inline] noncomputable def rcomp : (E⟿F)⟿(F⟿G)⟿(E⟿G) := curry ((uncurry comp).comp swap_pair)
    noncomputable def swap : (E⟿F⟿G)⟿(F⟿E⟿G) := curry.comp ((rcomp swap_pair).comp uncurry)

    @[simp] lemma const_apply : const x y = x := rfl
    @[simp] lemma swap_pair_apply  : swap_pair p = (p.2,p.1) := rfl
    @[simp] lemma rcomp_apply : rcomp g f = comp f g := rfl 
    @[simp] lemma swap_apply (f : E⟿F⟿G) : swap f y x = f x y := rfl 

    section differentials_of_basic_functions

      variables (df : F⟿G) (dg : E⟿F) (dx : E) (dy : F) (dp : E×F)

      /- These needs to be proven directly -/
      @[simp] lemma comp.arg3.diff_apply : δ (comp f g) x dx = δ f (g x) (δ g x dx) := sorry 
      @[simp] lemma curry.arg3.diff_apply (f : E×F⟿G) : δ (curry f x) y dy = δ f (x,y) (0,dy) := sorry
      @[simp] lemma curry.arg2.diff_apply (f : E×F⟿G) : δ (curry f) x dx y = δ f (x,y) (dx,0) := sorry
      @[simp] lemma uncurry.arg2.diff_apply (f : E⟿F⟿G) : δ (uncurry f) p dp = δ f p.1 dp.1 p.2 + δ (f p.1) p.2 dp.2 := sorry
      @[simp] lemma pair_map.arg3.diff_apply (f : E⟿G) (g : F⟿H) : δ (pair_map f g) p dp = (δ f p.1 dp.1, δ g p.2 dp.2) := sorry


      /- Differential of linear map is linear map its self, This will be easily proven once this general statemet is proven -/ 
      @[simp] lemma id.diff_apply : δ (id : E⟿E) x dx = id dx := sorry
      @[simp] lemma fst.diff_apply : δ (fst : E×F⟿E) p dp = fst dp := sorry
      @[simp] lemma snd.diff_apply : δ (snd : E×F⟿F) p dp = snd dp := sorry
      @[simp] lemma diag.diff_apply : δ (diag : E⟿E×E) x dx = diag dx := sorry
      @[simp] lemma assocr.diff_apply (t dt : (E×F)×G) : δ (assocr) t dt = assocr dt := sorry
      @[simp] lemma assocl.diff_apply (t dt : E×(F×G)) : δ (assocl) t dt = assocl dt := sorry
      @[simp] lemma perm.ba.diff_apply (p dp : E×F) : δ perm.ba p dp = perm.ba dp := sorry
      @[simp] lemma perm.ac_bd.diff_apply (p dp : (E×F)×(G×H)) : δ perm.ac_bd p dp = perm.ac_bd dp := sorry
      @[simp] lemma perm.ad_bc.diff_apply (p dp : (E×F)×(G×H)) : δ perm.ad_bc p dp = perm.ad_bc dp := sorry

      /- also linear maps  -/
      @[simp] lemma comp.arg1.diff_apply : δ comp f df g x = df (g x) := sorry
      @[simp] lemma curry.arg1.diff_apply (f df : E×F⟿G) : δ curry f df x y = df (x,y) := sorry
      @[simp] lemma uncurry.arg1.diff_apply (f df : E⟿F⟿G) : δ (uncurry) f df p = df p.1 p.2 := sorry


      @[simp] lemma eval.diff_apply (fx dfx : (E⟿F)×E) : δ eval fx dfx = (δ (fx.1)) fx.2 dfx.2 + dfx.1 fx.2 := begin unfold eval, simp, abel, end
      @[simp] lemma comp.arg2.diff_apply : δ (comp f) g dg x= δ f (g x) (dg x) := begin unfold comp, simp, end

      @[simp] lemma pair_map.arg1.diff_apply (f df : E⟿G) (g : F⟿H) : δ (pair_map) f df g p = (df p.1, 0) := begin unfold pair_map, simp, end
      @[simp] lemma pair_map.arg2.diff_apply (f : E⟿G) (g dg : F⟿H) : δ (pair_map f) g dg p = (0, dg p.2) := begin unfold pair_map, simp, end

      @[simp] lemma pair.arg2.diff_apply : δ (pair x) y dy = (0,dy) := begin unfold pair, simp, end
      @[simp] lemma pair.arg1.diff_apply : δ (pair) x dx y = (dx,0) := begin unfold pair, simp, end

      @[simp] lemma const.arg2.diff_apply  : δ (const x) y dy = 0 := begin unfold const, simp end
      @[simp] lemma const.arg1.diff_apply  : δ (const) x dx y = dx := begin unfold const, simp end
      @[simp] lemma swap_pair.diff_apply : δ swap_pair p dp = swap_pair dp := begin unfold swap_pair, simp, end
      @[simp] lemma swap.arg3.diff_apply (f : E⟿F⟿G) : δ (swap f y) x dx = δ f x dx y := begin unfold swap, simp, end
      @[simp] lemma swap.arg2.diff_apply (f : E⟿F⟿G) : δ (swap f) y dy x = δ (f x) y dy := begin unfold swap, simp, end
      @[simp] lemma swap.arg1.diff_apply (f df : E⟿F⟿G) : δ (swap) f df y x = df x y := begin unfold swap, simp, end
      

    end differentials_of_basic_functions

  end smooth

end convenient


