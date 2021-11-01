module Data.Double.FloatUtils.Chez

import Data.DPair
import Data.Fin
import Libraries.Utils.Scheme

%default total


rebool1 : (a -> Int) -> (a -> Bool)
rebool1 f = \x => (f x) == 1

rebool2 : (a -> a -> Int) -> (a -> a -> Bool)
rebool2 f = \x,y => (f x y) == 1

rebool3 : (a -> a -> a -> Int) -> (a -> a -> a -> Bool)
rebool3 f = \x,y,z => (f x y z) == 1

rebool4 : (a -> a -> a -> a -> Int) -> (a -> a -> a -> a -> Bool)
rebool4 f = \w,x,y,z => (f w x y z) == 1


namespace Vector
  data ForeignVector : Nat -> Type -> Type where
    [external]

  public export
  0 Vector : Nat -> Type -> Type
  Vector n ty = Ptr $ ForeignVector n ty

  %foreign "scheme,chez:idris-vector-ref"
  prim__vectorRef : Vector n ty -> Fin n -> ty

  export
  vectorRef : (i : Fin n) -> (v : Vector n ty) -> ty
  vectorRef i v = prim__vectorRef v i


namespace Misc
  export
  %foreign "scheme,chez:fllp"
  fllp : Double -> Int


  %foreign "scheme,chez:idris-+nan.0"
  prim__positiveNaN : Double

  %foreign "scheme,chez:idris-+inf.0"
  prim__positiveInf : Double

  %foreign "scheme,chez:idris--inf.0"
  prim__negativeInf : Double

  %foreign "scheme,chez:idris-isnan"
  prim__isNan : Double -> Int

  %foreign "scheme,chez:idris-notnan"
  prim__notNan : Double -> Int

  export
  nan : Double
  nan = prim__positiveNaN

  export
  isNan : Double -> Bool
  isNan = rebool1 prim__isNan

  export
  notNan : Double -> Bool
  notNan = rebool1 prim__notNan

  export
  inf : Double
  inf = prim__positiveInf

  -- Kind of redundant, because we have Neg Double, so we can write `- inf`
  export
  negInf : Double
  negInf = prim__negativeInf


  0 invertIsNan : forall x. not (isNan x) = True -> notNan x = True
  invertIsNan = believe_me

  0 invertNotNan : forall x. not (notNan x) = True -> isNan x = True
  invertNotNan = believe_me


  %foreign "scheme,chez:idris-flnonpositive"
  prim__isNonPositive : Double -> Int

  export
  isNonPositive : Double -> Bool
  isNonPositive = rebool1 prim__isNonPositive


  %foreign "scheme,chez:idris-flnonnegative"
  prim__isNonNegative : Double -> Int

  export
  isNonNegative : Double -> Bool
  isNonNegative = rebool prim__isNonNegative


  public export
  record DoubleInfo where
    constructor MkDoubleInfo
    mantissa : Int
    exponent : Int
    sign : Int

  %foreign "scheme,chez:decode-float"
  prim__decodeDouble : Double -> Vector 3 Int

  decodeDouble : (x : Double) -> DoubleInfo
  decodeDouble x =
    let result = prim__decodeDouble x in
      MkDoubleInfo
        (vectorRef 0 result)
        (vectorRef 1 result)
        (vectorRef 2 result)


namespace Comparison
  %foreign "scheme,chez:idris-compare"
  prim__compare : Double -> Double -> Int

  %foreign "scheme,chez:idris-fl=-2"
  prim__doubleEq2 : Double -> Double -> Int
  %foreign "scheme,chez:idris-fl=-3"
  prim__doubleEq3 : Double -> Double -> Double -> Int
  %foreign "scheme,chez:idris-fl=-4"
  prim__doubleEq4 : Double -> Double -> Double -> Double -> Int

  export
  doubleEq2 : Double -> Double -> Bool
  doubleEq2 = rebool2 prim__doubleEq2
  export
  doubleEq3 : Double -> Double -> Double -> Bool
  doubleEq3 = rebool3 prim__doubleEq3
  export
  doubleEq4 : Double -> Double -> Double -> Double -> Bool
  doubleEq4 = rebool4 prim__doubleEq4

  %foreign "scheme,chez:idris-fl>-2"
  prim__doubleGt2 : Double -> Double -> Int
  %foreign "scheme,chez:idris-fl>-3"
  prim__doubleGt3 : Double -> Double -> Double -> Int
  %foreign "scheme,chez:idris-fl>-4"
  prim__doubleGt4 : Double -> Double -> Double -> Double -> Int

  export
  doubleGt2 : Double -> Double -> Bool
  doubleGt2 = rebool2 prim__doubleGt2
  export
  doubleGt3 : Double -> Double -> Double -> Bool
  doubleGt3 = rebool3 prim__doubleGt3
  export
  doubleGt4 : Double -> Double -> Double -> Double -> Bool
  doubleGt4 = rebool4 prim__doubleGt4

  %foreign "scheme,chez:idris-fl>=-2"
  prim__doubleGte2 : Double -> Double -> Int
  %foreign "scheme,chez:idris-fl>=-3"
  prim__doubleGte3 : Double -> Double -> Double -> Int
  %foreign "scheme,chez:idris-fl>=-4"
  prim__doubleGte4 : Double -> Double -> Double -> Double -> Int

  export
  doubleGte2 : Double -> Double -> Bool
  doubleGte2 = rebool2 prim__doubleGte2
  export
  doubleGte3 : Double -> Double -> Double -> Bool
  doubleGte3 = rebool3 prim__doubleGte3
  export
  doubleGte4 : Double -> Double -> Double -> Double -> Bool
  doubleGte4 = rebool4 prim__doubleGte4

  %foreign "scheme,chez:idris-fl<-2"
  prim__doubleLt2 : Double -> Double -> Int
  %foreign "scheme,chez:idris-fl<-3"
  prim__doubleLt3 : Double -> Double -> Double -> Int
  %foreign "scheme,chez:idris-fl<-4"
  prim__doubleLt4 : Double -> Double -> Double -> Double -> Int

  export
  doubleLt2 : Double -> Double -> Bool
  doubleLt2 = rebool2 prim__doubleLt2
  export
  doubleLt3 : Double -> Double -> Double -> Bool
  doubleLt3 = rebool3 prim__doubleLt3
  export
  doubleLt4 : Double -> Double -> Double -> Double -> Bool
  doubleLt4 = rebool4 prim__doubleLt4

  %foreign "scheme,chez:idris-fl<=-2"
  prim__doubleLte2 : Double -> Double -> Int
  %foreign "scheme,chez:idris-fl<=-3"
  prim__doubleLte3 : Double -> Double -> Double -> Int
  %foreign "scheme,chez:idris-fl<=-4"
  prim__doubleLte4 : Double -> Double -> Double -> Double -> Int

  export
  doubleLte2 : Double -> Double -> Bool
  doubleLte2 = rebool2 prim__doubleLte2
  export
  doubleLte3 : Double -> Double -> Double -> Bool
  doubleLte3 = rebool3 prim__doubleLte3
  export
  doubleLte4 : Double -> Double -> Double -> Double -> Bool
  doubleLte4 = rebool4 prim__doubleLte4

  export
  %foreign "scheme,chez:max"
  doubleMax2 : Double -> Double -> Double
  export
  %foreign "scheme,chez:max"
  doubleMax3 : Double -> Double -> Double -> Double
  export
  %foreign "scheme,chez:max"
  doubleMax4 : Double -> Double -> Double -> Double -> Double

  export
  %foreign "scheme,chez:min"
  doubleMin2 : Double -> Double -> Double
  export
  %foreign "scheme,chez:min"
  doubleMin3 : Double -> Double -> Double -> Double
  export
  %foreign "scheme,chez:min"
  doubleMin4 : Double -> Double -> Double -> Double -> Double

  public export
  implementation [chezFloat] Ord Double where
    compare x y =
      if x < y 
      then LT
      else
        if x > y
        then GT
        else EQ
    (<) = doubleLt2
    (>) = doubleGt2
    (<=) = doubleLte2
    (>=) = doubleGte2
    max = doubleMax2
    min = doubleMin2

  namespace NanSafe
    0 DoubleNotNan : Type
    DoubleNotNan = Subset Double (\x => notNan x = True)

    -- implementation Functor DoubleNotNan where
    --   map f (Element x px) = ?help

    unwrap : DoubleNotNan -> Double
    unwrap (Element x _) = x

    wrap1 : (Double -> a) -> (DoubleNotNan -> a)
    wrap1 f = \ (Element x _) => f x

    wrap2 : (Double -> Double -> a) -> (DoubleNotNan -> DoubleNotNan -> a)
    wrap2 f = \ (Element x _), (Element y _) => f x y

    export
    doubleCompareSafe : DoubleNotNan -> DoubleNotNan -> Ordering
    doubleCompareSafe (Element x _) (Element y _) =
      assert_total $ case prim__compare x y of
        1 => GT
        -1 => LT
        0 => EQ

    export
    doubleLt2Safe : DoubleNotNan -> DoubleNotNan -> Bool
    doubleLt2Safe = wrap2 doubleLt2

    export
    doubleGt2Safe : DoubleNotNan -> DoubleNotNan -> Bool
    doubleGt2Safe = wrap2 doubleGt2

    export
    doubleLte2Safe : DoubleNotNan -> DoubleNotNan -> Bool
    doubleLte2Safe = wrap2 doubleLte2

    export
    doubleGte2Safe : DoubleNotNan -> DoubleNotNan -> Bool
    doubleGte2Safe = wrap2 doubleGte2

    export
    doubleMax2Safe : DoubleNotNan -> DoubleNotNan -> DoubleNotNan
    doubleMax2Safe = believe_me $ wrap2 doubleMax2

    export
    doubleMin2Safe : DoubleNotNan -> DoubleNotNan -> DoubleNotNan
    doubleMin2Safe = believe_me $ wrap2 doubleMin2

    public export
    implementation [chezFloatNanSafe] Ord DoubleNotNan where
      compare = doubleCompareSafe
      (<) = wrap2 doubleLt2
      (>) = wrap2 doubleGt2
      (<=) = wrap2 doubleLte2
      (>=) = wrap2 doubleGte2
      max = believe_me $ wrap2 doubleMax2
      min = believe_me $ wrap2 doubleMin2

  namespace List
    %foreign "scheme,chez:idris-fl=-apply"
    prim__doubleEq : List Double -> Int
    %foreign "scheme,chez:idris-fl>-apply"
    prim__doubleGt : List Double -> Int
    %foreign "scheme,chez:idris-fl>=-apply"
    prim__doubleGte : List Double -> Int
    %foreign "scheme,chez:idris-fl<-apply"
    prim__doubleLt : List Double -> Int
    %foreign "scheme,chez:idris-fl<=-apply"
    prim__doubleLte : List Double -> Int

    export
    doubleEq : List Double -> Bool
    doubleEq xs = (prim__doubleEq xs) == 1
    export
    doubleGt : List Double -> Bool
    doubleGt xs = (prim__doubleGt xs) == 1
    export
    doubleGte : List Double -> Bool
    doubleGte xs = (prim__doubleGte xs) == 1
    export
    doubleLt : List Double -> Bool
    doubleLt xs = (prim__doubleLt xs) == 1
    export
    doubleLte : List Double -> Bool
    doubleLte xs = (prim__doubleLte xs) == 1

    export
    %foreign "scheme,chez:idris-max-apply"
    doubleMax : List Double -> Double
    export
    %foreign "scheme,chez:idris-min-apply"
    doubleMin : List Double -> Double


implementation Show Ordering where
  show LT = "LT"
  show EQ = "EQ"
  show GT = "GT"

implementation Interpolation Int where
  interpolate = show

implementation Interpolation Ordering where
  interpolate = show


-- %foreign "scheme:idris-bad"
-- bad : () -> Nat

test : IO ()
test = do
  -- printLn $ bad ()
  printLn $ isNonNegative 3.6
  printLn $ doubleEq [1.5, 1.5]
  printLn $ doubleMax [1.5, 1.5, 2.5]
  printLn $ 1.5 == 1.5
  let out = decodeDouble 4.5
  printLn "m=\{out.mantissa} e=\{out.exponent} s\{out.sign}"
