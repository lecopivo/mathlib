import analysis.normed_space.inner_product

import analysis.convenient_space.differential


reserve prefix `∇`: 1500


namespace convenient

  section gradient
    variables 
      {E : Type*} [inner_product_space ℝ E] [locally_convex_space ℝ E]
      {F : Type*} [inner_product_space ℝ F] [locally_convex_space ℝ F] 
      {G : Type*} [inner_product_space ℝ G] [locally_convex_space ℝ G] 
    
    def grad : (E⟿ℝ)⟿(E⟿E) := sorry

    notation ∇ f := grad f

    @[simp] def grad_app (f : E⟿ℝ) (x v : E) : ⟪∇ f x, v⟫_ℝ = δ f x v := sorry

  end gradient

end convenient
