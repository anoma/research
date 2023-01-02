module Library.Test.TestLibrary

import public Library.Decidability
import public RefinedSExp.Data

%default total

public export
Assertion : Type
Assertion = ()

public export
Assert : (b : Bool) -> if b then () else List ()
Assert True = ()
Assert False = []

-- Provide a "default" primitive type.

public export
data PrimitiveType : Type where
  PrimTypeBool : PrimitiveType
  PrimTypeNat : PrimitiveType
  PrimTypeString : PrimitiveType

-- Haskell can just derive this.
export
primTypeEq : (primType, primType' : PrimitiveType) -> Dec (primType = primType')
primTypeEq PrimTypeBool PrimTypeBool = Yes Refl
primTypeEq PrimTypeBool PrimTypeNat = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeBool PrimTypeString = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeNat PrimTypeBool = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeNat PrimTypeNat = Yes Refl
primTypeEq PrimTypeNat PrimTypeString = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeBool = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeNat = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeString = Yes Refl

public export
interpretPrimitiveType : PrimitiveType -> Type
interpretPrimitiveType PrimTypeBool = Bool
interpretPrimitiveType PrimTypeNat = Nat
interpretPrimitiveType PrimTypeString = String

public export
primitiveEq : (primType : PrimitiveType) ->
  (x, x' : interpretPrimitiveType primType) -> Dec (x = x')
primitiveEq PrimTypeBool = decEq
primitiveEq PrimTypeNat = decEq
primitiveEq PrimTypeString = decEq

public export
PrimitiveExp : Type
PrimitiveExp = DPair PrimitiveType interpretPrimitiveType

public export
primExpEq : (primExp, primExp' : PrimitiveExp) -> Dec (primExp = primExp')
primExpEq (primType ** primExp) (primType' ** primExp') with
  (primTypeEq primType primType')
    primExpEq (primType ** primExp) (primType ** primExp') | Yes Refl =
      case primitiveEq primType primExp primExp' of
        Yes Refl => Yes Refl
        No neq => No (\eq => case eq of Refl => neq Refl)
    primExpEq (primType ** primExp) (primType' ** primExp') | No neq =
      No (\eq => case eq of Refl => neq Refl)

public export
Show PrimitiveExp where
  show (PrimTypeBool ** b) = show b
  show (PrimTypeNat ** n) = show n
  show (PrimTypeString ** s) = s
