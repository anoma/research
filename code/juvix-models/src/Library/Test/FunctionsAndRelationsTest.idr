module Library.Test.FunctionsAndRelationsTest

import public Library.FunctionsAndRelations
import Data.Vect

%default total

Telescope_type_1 : Type
Telescope_type_1 = Nat

Telescope_test_1 : Telescope
Telescope_test_1 = |- Telescope_type_1

Telescope_type_2 : Telescope_type_1 -> Type
Telescope_type_2 = flip Vect String

Telescope_test_2 : Telescope
Telescope_test_2 = Telescope_test_1 *~ Telescope_type_2

Telescope_test_2_correct :
  Telescope_test_2 = |- Telescope_type_1 *~ Telescope_type_2
Telescope_test_2_correct = Refl

Telescope_type_3 : DPair Telescope_type_1 Telescope_type_2 -> Type
Telescope_type_3 (n ** v) = Vect (S n) Nat

Telescope_test_3 : Telescope
Telescope_test_3 = Telescope_test_2 *~ Telescope_type_3

Telescope_test_3_correct : Telescope_test_3 =
  |- Telescope_type_1 *~ Telescope_type_2 *~ Telescope_type_3
Telescope_test_3_correct = Refl

telescope_val_1 : :~ Telescope_test_1
telescope_val_1 = 2

telescope_val_2 : :~ Telescope_test_2
telescope_val_2 = (telescope_val_1 ** ["hi", "there"])

telescope_val_3 : :~ Telescope_test_3
telescope_val_3 = (2 **< ["hi", "there"] **< [2, 5, 99])

test_string_table : Nat -> String
test_string_table 0 = "hi"
test_string_table 1 = "there"
test_string_table 2 = "someone"
test_string_table _ = "undefined"

telescope_fn_12 : Telescope_test_1 :~> Telescope_type_2
telescope_fn_12 0 = []
telescope_fn_12 (S n) = snoc (telescope_fn_12 n) (test_string_table n)

telescope_fn_12_correct :
 (Library.Test.FunctionsAndRelationsTest.telescope_val_1 **~
  Library.Test.FunctionsAndRelationsTest.telescope_fn_12) =
 Library.Test.FunctionsAndRelationsTest.telescope_val_2
telescope_fn_12_correct = Refl

telescope_fn_23 : Telescope_test_2 :~> Telescope_type_3
telescope_fn_23 (n ** v) = snoc (map length v) 99

telescope_fn_23_correct :
 (Library.Test.FunctionsAndRelationsTest.telescope_val_2 **~
  Library.Test.FunctionsAndRelationsTest.telescope_fn_23) =
 Library.Test.FunctionsAndRelationsTest.telescope_val_3
telescope_fn_23_correct = Refl

telescope_fn_13 :
  Telescope_test_1 :~>
  (Telescope_type_3 .** Library.Test.FunctionsAndRelationsTest.telescope_fn_12)
telescope_fn_13 = (:.~) {a=Telescope_test_1} telescope_fn_23 telescope_fn_12

telescope_fn_13_correct :
  (Library.Test.FunctionsAndRelationsTest.telescope_fn_13
   Library.Test.FunctionsAndRelationsTest.telescope_val_1) =
  snd Library.Test.FunctionsAndRelationsTest.telescope_val_3
telescope_fn_13_correct = Refl
