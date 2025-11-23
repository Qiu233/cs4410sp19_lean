abbrev ContT (γ : Type) (m : Type → Type) (α : Type) := (α → m γ) → m γ

def ContT.run {γ : Type} {m : Type → Type} {α : Type} (cont : ContT γ m α) (f : α → m γ) : m γ := cont f

def ContT.pure {m : Type → Type} : α → ContT γ m α := fun a k => k a

def ContT.bind {m : Type → Type} : ContT γ m α → (α → ContT γ m β) → ContT γ m β := fun a' f k => a' (fun a => f a k)

@[always_inline]
instance [Monad m] : Monad (ContT γ m) where
  pure := ContT.pure
  bind := ContT.bind

@[always_inline]
instance [Bind m] : MonadLiftT m (ContT γ m) where
  monadLift a' k := a' >>= k

@[always_inline]
instance [Bind m] : MonadLift m (ContT γ m) where
  monadLift a' k := a' >>= k
