﻿namespace MathNet.Symbolics

open System
open MathNet.Numerics
open MathNet.Symbolics

type BigInteger = System.Numerics.BigInteger

type ComplexBigRational = {
    Real: BigRational
    Imaginary: BigRational
}

[<RequireQualifiedAccess>]
module internal FromPrimitive =
    let inline complex32 (x:complex32) = complex (float x.Real) (float x.Imaginary)
    let inline int32 (x:int) = BigRational.FromInt x
    let inline int64 (x:int64) = BigRational.FromBigInt (BigInteger x)
    let inline bigint (x:BigInteger) = BigRational.FromBigInt x

[<RequireQualifiedAccess>]
type NewValue =
    | Exact of ExactValue
    | RealApprox of float
    | ComplexApprox of complex


[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module NewValue =

    let fromInt32 (x:int) = NewValue.Exact (ExactValue.fromInt32 x)
    let fromInt64 (x:int64) = NewValue.Exact (ExactValue.fromInt64 x)
    let fromInteger (x:BigInteger) = NewValue.Exact (ExactValue.fromInteger x)
    let fromIntegerFraction (n:BigInteger) (d:BigInteger) = NewValue.Exact (ExactValue.fromIntegerFraction n d)
    let fromRational (x:BigRational) = NewValue.Exact (ExactValue.fromRational x)
    let fromComplexInt32 (real:int) (imag:int) = NewValue.Exact (ExactValue.fromComplexInt32 real imag)
    let fromComplexInt64 (real:int64) (imag:int64) = NewValue.Exact (ExactValue.fromComplexInt64 real imag)
    let fromComplexInteger (real:BigInteger) (imag:BigInteger) = NewValue.Exact (ExactValue.fromComplexInteger real imag)
    let fromComplexRational (real:BigRational) (imag:BigRational) = NewValue.Exact (ExactValue.fromComplexRational real imag)

    let fromReal (x:float) =
        if Double.IsPositiveInfinity x then NewValue.PositiveInfinity
        elif Double.IsNegativeInfinity x then NewValue.NegativeInfinity
        elif Double.IsNaN x then NewValue.Undefined
        else NewValue.RealApprox x

    let fromReal32 (x:float32) =
        if Single.IsPositiveInfinity x then NewValue.PositiveInfinity
        elif Single.IsNegativeInfinity x then NewValue.NegativeInfinity
        elif Single.IsNaN x then NewValue.Undefined
        else NewValue.RealApprox (float x)

    let fromComplex (x:complex) =
        if x.IsReal() then fromReal x.Real
        elif x.IsInfinity() then NewValue.ComplexInfinity
        elif x.IsNaN() then NewValue.Undefined
        else NewValue.ComplexApprox x

    let fromComplex32 (x:complex32) =
        if x.IsReal() then fromReal32 x.Real
        elif x.IsInfinity() then NewValue.ComplexInfinity
        elif x.IsNaN() then NewValue.Undefined
        else NewValue.ComplexApprox (FromPrimitive.complex32 x)

    let fromConstant (c:Constant) = NewValue.Constant c

    let fromExact (x:ExactValue) = NewValue.Exact x

    let zero = NewValue.Rational BigRational.Zero
    let one = NewValue.Rational BigRational.One
    let minusOne = NewValue.Rational (BigRational.FromInt -1)


    let (|Zero|_|) = function
        | NewValue.Rational n when n.IsZero -> Some Zero
        | NewValue.RealApprox x when x = 0.0 -> Some Zero
        | NewValue.ComplexApprox x when x.IsZero() -> Some Zero
        | _ -> None

    let (|One|_|) = function
        | NewValue.Rational n when n.IsOne -> Some One
        | NewValue.ComplexRational n when n.Real.IsOne && n.Imaginary.IsZero -> Some One
        | _ -> None

    let (|MinusOne|_|) = function
        | NewValue.Rational n when n.IsInteger && n.Numerator = BigInteger.MinusOne -> Some MinusOne
        | NewValue.ComplexRational n when n.Real.IsInteger && n.Real.Numerator = BigInteger.MinusOne && n.Imaginary.IsZero -> Some MinusOne
        | _ -> None

    let (|ApproxOne|_|) = function
        | One _ -> Some ApproxOne
        | NewValue.RealApprox x when x = 1.0 -> Some ApproxOne
        | NewValue.ComplexApprox x when x = Complex.one -> Some ApproxOne
        | _ -> None

    let (|ApproxMinusOne|_|) = function
        | MinusOne _ -> Some ApproxMinusOne
        | NewValue.RealApprox x when x = -1.0 -> Some ApproxMinusOne
        | NewValue.ComplexApprox x when x.IsReal() && x.Real = -1.0 -> Some ApproxMinusOne
        | _ -> None

    let (|Positive|_|) = function
        | NewValue.Rational n when n.IsPositive -> Some Positive
        | NewValue.ComplexRational n when n.Real.IsPositive && n.Imaginary.IsZero -> Some Positive
        | NewValue.RealApprox x when x > 0.0 -> Some Positive
        | NewValue.ComplexApprox x when x.IsReal() && x.Real > 0.0-> Some Positive
        | NewValue.PositiveInfinity -> Some Positive
        | NewValue.Constant E | NewValue.Constant Pi -> Some Positive
        | _ -> None

    let (|Negative|_|) = function
        | NewValue.Rational n when n.IsNegative -> Some Negative
        | NewValue.ComplexRational n when n.Real.IsNegative && n.Imaginary.IsZero -> Some Negative
        | NewValue.RealApprox x when x < 0.0 -> Some Negative
        | NewValue.ComplexApprox x when x.IsReal() && x.Real < 0.0 -> Some Negative
        | NewValue.NegativeInfinity -> Some Negative
        | _ -> None

    let (|Approximation|Exact|) = function
        | NewValue.RealApprox _ | NewValue.ComplexApprox _ -> Approximation
        | _ -> Exact

    let isZero = function | Zero -> true | _ -> false
    let isOne = function | One -> true | _ -> false
    let isMinusOne = function | MinusOne -> true | _ -> false
    let isPositive = function | Positive -> true | _ -> false
    let isNegative = function | Negative -> true | _ -> false
    let isApproxOne = function | ApproxOne -> true | _ -> false
    let isApproxMinusOne = function | ApproxMinusOne -> true | _ -> false
    let isApproximation = function | Approximation -> true | _ -> false
    let isExact = function | Exact -> true | _ -> false

    let resolveConstant = function
        | E -> NewValue.RealApprox Constants.E
        | Pi -> NewValue.RealApprox Constants.Pi
        | I -> NewValue.ComplexApprox Complex.onei

    let approximate = function
        | ExactValue.Rational a -> NewValue.RealApprox (float a)
        | ExactValue.ComplexRational a -> NewValue.ComplexApprox (complex (float a.Real) (float a.Imaginary))
        | ExactValue.Constant c -> resolveConstant c
        | ExactValue.DirectedConstant (c, ComplexBigRational.RealRational r) ->
            match resolveConstant c with
            | NewValue.RealApprox x -> (float r) * x |> fromReal
            | NewValue.ComplexApprox x -> (float r) * x |> fromComplex
        | ExactValue.DirectedConstant (c, ComplexBigRational.Complex (r,i)) ->
            let fr = float r
            let fi = float i
            match resolveConstant c with
            | NewValue.RealApprox x -> complex (fr * x) (fi * x) |> fromComplex
            | NewValue.ComplexApprox x -> complex (fr * x.Real - fi * x.Imaginary) (fr * x.Imaginary + fi * x.Real) |> fromComplex
        | ExactValue.NegativeInfinity -> NewValue.Exact ExactValue.NegativeInfinity
        | ExactValue.PositiveInfinity -> NewValue.Exact ExactValue.PositiveInfinity
        | ExactValue.DirectedInfinity _ as x -> NewValue.Exact x
        | ExactValue.ComplexInfinity -> NewValue.Exact ExactValue.ComplexInfinity
        | ExactValue.Undefined -> NewValue.Exact ExactValue.Undefined

    let rec negate = function
        | NewValue.Rational a -> NewValue.Rational (-a)
        | NewValue.RealApprox a -> NewValue.RealApprox (-a)
        | NewValue.ComplexApprox a -> NewValue.ComplexApprox (-a)
        | NewValue.NegativeInfinity -> NewValue.PositiveInfinity
        | NewValue.PositiveInfinity -> NewValue.NegativeInfinity
        | NewValue.ComplexInfinity -> NewValue.ComplexInfinity
        | NewValue.Undefined -> NewValue.Undefined
        | NewValue.Constant c -> resolveConstant c |> negate

    let rec abs = function
        | NewValue.Rational a when a.IsNegative -> NewValue.Rational (-a)
        | NewValue.Rational _ as x -> x
        | NewValue.RealApprox a -> Math.Abs a |> fromReal
        | NewValue.ComplexApprox a -> Complex.magnitude a |> fromReal
        | NewValue.NegativeInfinity | NewValue.PositiveInfinity | NewValue.ComplexInfinity -> NewValue.PositiveInfinity
        | NewValue.Undefined -> NewValue.Undefined
        | NewValue.Constant I -> one
        | NewValue.Constant c -> resolveConstant c |> abs

    let rec sum = function
        | NewValue.Undefined, _ | _, NewValue.Undefined -> NewValue.Undefined
        | Zero, b | b, Zero -> b
        | NewValue.Rational a, NewValue.Rational b -> NewValue.Rational (a + b)
        | NewValue.RealApprox a, NewValue.RealApprox b -> a + b |> fromReal
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> a + b |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b | NewValue.RealApprox b, NewValue.ComplexApprox a -> a + (complex b 0.0) |> fromComplex
        | NewValue.Rational a, NewValue.RealApprox b | NewValue.RealApprox b, NewValue.Rational a -> (float a) + b |> fromReal
        | NewValue.Rational a, NewValue.ComplexApprox b | NewValue.ComplexApprox b, NewValue.Rational a -> (complex (float a) 0.0) + b |> fromComplex
        | NewValue.ComplexInfinity, (NewValue.ComplexInfinity | NewValue.PositiveInfinity | NewValue.NegativeInfinity) -> NewValue.Undefined
        | (NewValue.ComplexInfinity | NewValue.PositiveInfinity | NewValue.NegativeInfinity),  NewValue.ComplexInfinity -> NewValue.Undefined
        | NewValue.ComplexInfinity, _ | _, NewValue.ComplexInfinity -> NewValue.ComplexInfinity
        | NewValue.PositiveInfinity, NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | NewValue.PositiveInfinity, NewValue.NegativeInfinity | NewValue.NegativeInfinity, NewValue.PositiveInfinity -> NewValue.Undefined
        | NewValue.PositiveInfinity, _ | _, NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | NewValue.NegativeInfinity, NewValue.NegativeInfinity -> NewValue.NegativeInfinity
        | NewValue.NegativeInfinity, _ | _, NewValue.NegativeInfinity -> NewValue.NegativeInfinity
        | NewValue.Constant a, b -> sum (resolveConstant a, b)
        | a, NewValue.Constant b -> sum (a, resolveConstant b)

    let rec product = function
        | NewValue.Undefined, _ | _, NewValue.Undefined -> NewValue.Undefined
        | One, b | b, One -> b
        | Zero, (NewValue.ComplexInfinity | NewValue.PositiveInfinity | NewValue.NegativeInfinity) -> NewValue.Undefined
        | (NewValue.ComplexInfinity | NewValue.PositiveInfinity | NewValue.NegativeInfinity), Zero -> NewValue.Undefined
        | Zero, _ | _, Zero -> zero
        | NewValue.Rational a, NewValue.Rational b -> NewValue.Rational (a * b)
        | NewValue.RealApprox a, NewValue.RealApprox b -> a * b |> fromReal
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> a * b |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b | NewValue.RealApprox b, NewValue.ComplexApprox a -> a * (complex b 0.0) |> fromComplex
        | NewValue.Rational a, NewValue.RealApprox b | NewValue.RealApprox b, NewValue.Rational a -> (float a) * b |> fromReal
        | NewValue.Rational a, NewValue.ComplexApprox b | NewValue.ComplexApprox b, NewValue.Rational a -> (complex (float a) 0.0) * b |> fromComplex
        | NewValue.ComplexInfinity, _ | _, NewValue.ComplexInfinity -> NewValue.ComplexInfinity
        | NewValue.PositiveInfinity, Positive | Positive, NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | NewValue.PositiveInfinity, Negative | Negative, NewValue.PositiveInfinity -> NewValue.NegativeInfinity
        | NewValue.NegativeInfinity, Positive | Positive, NewValue.NegativeInfinity -> NewValue.NegativeInfinity
        | NewValue.NegativeInfinity, Negative | Negative, NewValue.NegativeInfinity -> NewValue.PositiveInfinity
        | NewValue.NegativeInfinity, _ | _, NewValue.NegativeInfinity -> NewValue.NegativeInfinity
        | NewValue.PositiveInfinity, _ | _, NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | NewValue.Constant a, b -> product (resolveConstant a, b)
        | a, NewValue.Constant b -> product (a, resolveConstant b)

    let rec invert = function
        | Zero -> NewValue.ComplexInfinity
        | NewValue.Rational a -> NewValue.Rational (BigRational.Reciprocal a)
        | NewValue.RealApprox a -> 1.0 / a |> fromReal
        | NewValue.ComplexApprox a -> Complex.one / a |> fromComplex
        | NewValue.ComplexInfinity | NewValue.PositiveInfinity | NewValue.NegativeInfinity -> zero
        | NewValue.Undefined -> NewValue.Undefined
        | NewValue.Constant c -> resolveConstant c |> invert

    let rec power = function
        | NewValue.Undefined, _ | _, NewValue.Undefined -> NewValue.Undefined
        | Zero, Zero -> NewValue.Undefined
        | Zero, (NewValue.ComplexInfinity | NewValue.PositiveInfinity) -> zero
        | Zero, NewValue.NegativeInfinity -> NewValue.ComplexInfinity
        | Zero, Positive -> zero
        | Zero, Negative -> NewValue.ComplexInfinity
        | (NewValue.ComplexInfinity | NewValue.PositiveInfinity | NewValue.NegativeInfinity), Zero -> NewValue.Undefined
        | (NewValue.ComplexInfinity | NewValue.PositiveInfinity | NewValue.NegativeInfinity), NewValue.PositiveInfinity -> NewValue.ComplexInfinity
        | (NewValue.ComplexInfinity | NewValue.PositiveInfinity | NewValue.NegativeInfinity), NewValue.Rational b when b.IsNegative -> zero
        | NewValue.ComplexInfinity, Positive -> NewValue.ComplexInfinity
        | NewValue.PositiveInfinity, Positive -> NewValue.PositiveInfinity
        | NewValue.NegativeInfinity, NewValue.Rational b when b.IsPositive && b.IsInteger ->
            if (b.Numerator % 2I).IsZero then NewValue.PositiveInfinity else NewValue.NegativeInfinity
        | One, (NewValue.ComplexInfinity | NewValue.PositiveInfinity | NewValue.NegativeInfinity) | MinusOne, (NewValue.ComplexInfinity | NewValue.PositiveInfinity | NewValue.NegativeInfinity) -> NewValue.Undefined
        | One, _ | _, Zero -> one
        | _, Zero -> one
        | a, One -> a
        | One, _ -> one
        | Positive, NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | Negative, NewValue.PositiveInfinity -> NewValue.ComplexInfinity
        | _, NewValue.NegativeInfinity -> zero
        | _, NewValue.ComplexInfinity -> NewValue.Undefined
        | NewValue.Rational a, NewValue.Rational b when b.IsInteger ->
            if b.IsNegative then
                if a.IsZero then NewValue.ComplexInfinity
                // workaround bug in BigRational with negative powers - drop after upgrading to > v3.0.0-alpha9
                else NewValue.Rational (BigRational.Pow(BigRational.Reciprocal a, -int(b.Numerator)))
            else NewValue.Rational (BigRational.Pow(a, int(b.Numerator)))
        | NewValue.RealApprox a, NewValue.RealApprox b -> a**b |> fromReal
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> Complex.pow b a |> fromComplex
        | NewValue.RealApprox a, NewValue.ComplexApprox b -> Complex.pow b (complex a 0.0) |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b -> Complex.pow (complex b 0.0) a |> fromComplex
        | NewValue.Rational a, NewValue.Rational b -> (float a)**(float b) |> fromReal // TODO: must be a better way
        | NewValue.RealApprox a, NewValue.Rational b -> a**(float b) |> fromReal
        | NewValue.ComplexApprox a, NewValue.Rational b -> Complex.pow (complex (float b) 0.0) a |> fromComplex
        | NewValue.Rational a, NewValue.RealApprox b -> (float a)**b |> fromReal
        | NewValue.Rational a, NewValue.ComplexApprox b -> Complex.pow b (complex (float a) 0.0) |> fromComplex
        | NewValue.Constant a, b -> power (resolveConstant a, b)
        | a, NewValue.Constant b -> power (a, resolveConstant b)
        | _ -> NewValue.Undefined // TODO

    let rec ln = function
        | Zero -> NewValue.NegativeInfinity
        | One -> zero
        | NewValue.Constant E -> one
        | NewValue.RealApprox a -> Math.Log a |> fromReal
        | NewValue.ComplexApprox a -> Complex.ln a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> ln
        | NewValue.Constant c -> resolveConstant c |> ln
        | NewValue.ComplexInfinity -> NewValue.PositiveInfinity
        | NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | NewValue.NegativeInfinity -> NewValue.PositiveInfinity
        | NewValue.Undefined -> NewValue.Undefined

    let rec log10 = function
        | Zero -> NewValue.NegativeInfinity
        | One -> zero
        | NewValue.Rational n when n.Equals(10N) -> one
        | NewValue.RealApprox a -> Math.Log10 a |> fromReal
        | NewValue.ComplexApprox a -> Complex.log10 a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> log10
        | NewValue.Constant c -> resolveConstant c |> log10
        | NewValue.ComplexInfinity -> NewValue.PositiveInfinity
        | NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | NewValue.NegativeInfinity -> NewValue.PositiveInfinity
        | NewValue.Undefined -> NewValue.Undefined

    let log b x =
        match b, x with
        | NewValue.RealApprox v, NewValue.RealApprox w -> Math.Log (v, w) |> fromReal
        | NewValue.RealApprox v, NewValue.ComplexApprox w -> Complex.log v w |> fromComplex
        | _ -> failwith "not supported"

    let rec exp = function
        | Zero -> one
        | One -> NewValue.Constant E
        | MinusOne -> NewValue.Constant E |> invert
        | NewValue.RealApprox a -> Math.Exp a |> fromReal
        | NewValue.ComplexApprox a -> Complex.exp a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> log10
        | NewValue.Constant c -> resolveConstant c |> log10
        | NewValue.ComplexInfinity -> NewValue.Undefined
        | NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | NewValue.NegativeInfinity -> zero
        | NewValue.Undefined -> NewValue.Undefined


    let rec sin = function
        | NewValue.Exact x -> ExactValue.trySin x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> sin)
        | NewValue.RealApprox a -> Math.Sin a |> fromReal
        | NewValue.ComplexApprox a -> Complex.sin a |> fromComplex

    let rec cos = function
        | NewValue.Exact x -> ExactValue.tryCos x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> cos)
        | NewValue.RealApprox a -> Math.Cos a |> fromReal
        | NewValue.ComplexApprox a -> Complex.cos a |> fromComplex

    let rec tan = function
        | NewValue.Exact x -> ExactValue.tryTan x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> tan)
        | NewValue.RealApprox a -> Math.Tan a |> fromReal
        | NewValue.ComplexApprox a -> Complex.tan a |> fromComplex

    let rec csc = function
        | NewValue.Exact x -> ExactValue.tryCsc x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> csc)
        | NewValue.RealApprox a -> Trig.Csc a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Csc a |> fromComplex

    let rec sec = function
        | NewValue.Exact x -> ExactValue.trySec x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> sec)
        | NewValue.RealApprox a -> Trig.Sec a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Sec a |> fromComplex

    let rec cot = function
        | NewValue.Exact x -> ExactValue.tryCot x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> cot)
        | NewValue.RealApprox a -> Trig.Cot a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Cot a |> fromComplex


    let rec sinh = function
        | NewValue.Exact x -> ExactValue.trySinh x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> sinh)
        | NewValue.RealApprox a -> Trig.Sinh a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Sinh a |> fromComplex

    let rec cosh = function
        | NewValue.Exact x -> ExactValue.tryCosh x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> cosh)
        | NewValue.RealApprox a -> Trig.Cosh a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Cosh a |> fromComplex

    let rec tanh = function
        | NewValue.Exact x -> ExactValue.tryTanh x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> tanh)
        | NewValue.RealApprox a -> Trig.Tanh a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Tanh a |> fromComplex

    let rec csch = function
        | NewValue.Exact x -> ExactValue.tryCsch x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> csch)
        | NewValue.RealApprox a -> Trig.Csch a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Csch a |> fromComplex

    let rec sech = function
        | NewValue.Exact x -> ExactValue.trySech x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> sech)
        | NewValue.RealApprox a -> Trig.Sech a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Sech a |> fromComplex

    let rec coth = function
        | NewValue.Exact x -> ExactValue.tryCoth x |> Option.map fromExact |> Option.defaultWith (fun () -> approximate x |> coth)
        | NewValue.RealApprox a -> Trig.Coth a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Coth a |> fromComplex


    let rec asin = function
        | Zero -> zero
        | NewValue.RealApprox a -> Trig.Asin a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Asin a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> asin
        | NewValue.Constant c -> resolveConstant c |> asin
        | NewValue.PositiveInfinity -> NewValue.ComplexInfinity // actually: i*oo
        | NewValue.NegativeInfinity -> NewValue.ComplexInfinity // actually: -i*oo
        | NewValue.ComplexInfinity -> NewValue.ComplexInfinity
        | NewValue.Undefined -> NewValue.Undefined

    let rec acos = function
        | One -> zero
        | MinusOne -> NewValue.Constant Constant.Pi
        | NewValue.RealApprox a -> Trig.Acos a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Acos a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> acos
        | NewValue.Constant c -> resolveConstant c |> acos
        | NewValue.PositiveInfinity -> NewValue.ComplexInfinity // actually: -i*oo
        | NewValue.NegativeInfinity -> NewValue.ComplexInfinity // actually: i*oo
        | NewValue.ComplexInfinity -> NewValue.ComplexInfinity
        | NewValue.Undefined -> NewValue.Undefined

    let rec atan = function
        | Zero -> zero
        | NewValue.RealApprox a -> Trig.Atan a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Atan a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> atan
        | NewValue.Constant c -> resolveConstant c |> atan
        | NewValue.PositiveInfinity -> NewValue.RealApprox (Constants.PiOver2)
        | NewValue.NegativeInfinity -> NewValue.RealApprox (-Constants.PiOver2)
        | NewValue.Undefined | NewValue.ComplexInfinity -> NewValue.Undefined

    let atan2 x y =
        match x, y with
        | NewValue.RealApprox a, NewValue.RealApprox b -> Math.Atan2 (a, b) |> fromReal
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> Complex.atan (a / b) |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b -> Complex.atan (a / (complex b 0.0)) |> fromComplex
        | NewValue.RealApprox a, NewValue.ComplexApprox b -> Complex.atan (complex a 0.0) / b |> fromComplex

    let rec acsc = function
        | Zero -> NewValue.ComplexInfinity
        | NewValue.RealApprox a -> Trig.Acsc a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Acsc a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> acsc
        | NewValue.Constant c -> resolveConstant c |> acsc
        | NewValue.PositiveInfinity -> zero
        | NewValue.NegativeInfinity -> zero
        | NewValue.ComplexInfinity -> zero
        | NewValue.Undefined -> NewValue.Undefined

    let rec asec = function
        | Zero -> NewValue.ComplexInfinity
        | One -> zero
        | MinusOne -> NewValue.Constant Constant.Pi
        | NewValue.RealApprox a -> Trig.Asec a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Asec a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> asec
        | NewValue.Constant c -> resolveConstant c |> asec
        | NewValue.PositiveInfinity -> NewValue.RealApprox (Constants.PiOver2)
        | NewValue.NegativeInfinity -> NewValue.RealApprox (Constants.PiOver2)
        | NewValue.ComplexInfinity -> NewValue.RealApprox (Constants.PiOver2)
        | NewValue.Undefined -> NewValue.Undefined

    let rec acot = function
        | NewValue.RealApprox a -> Trig.Acot a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Acot a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> acot
        | NewValue.Constant c -> resolveConstant c |> acot
        | NewValue.PositiveInfinity -> zero
        | NewValue.NegativeInfinity -> zero
        | NewValue.ComplexInfinity -> zero
        | NewValue.Undefined -> NewValue.Undefined


    let rec asinh = function
        | NewValue.RealApprox a -> Trig.Asinh a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Asinh a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> asinh
        | NewValue.Constant c -> resolveConstant c |> asinh
        | NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | NewValue.NegativeInfinity -> NewValue.NegativeInfinity
        | NewValue.ComplexInfinity -> NewValue.ComplexInfinity
        | NewValue.Undefined -> NewValue.Undefined

    let rec acosh = function
        | NewValue.RealApprox a -> Trig.Acosh a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Acosh a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> acosh
        | NewValue.Constant c -> resolveConstant c |> acosh
        | NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | NewValue.NegativeInfinity -> NewValue.PositiveInfinity
        | NewValue.ComplexInfinity -> NewValue.PositiveInfinity
        | NewValue.Undefined -> NewValue.Undefined

    let rec atanh = function
        | NewValue.RealApprox a -> Trig.Atanh a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Atanh a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> atanh
        | NewValue.Constant c -> resolveConstant c |> atanh
        | NewValue.PositiveInfinity -> NewValue.ComplexApprox (complex 0.0 -Constants.PiOver2)
        | NewValue.NegativeInfinity -> NewValue.ComplexApprox (complex 0.0 Constants.PiOver2)
        | NewValue.Undefined | NewValue.ComplexInfinity -> NewValue.Undefined

    let rec acsch = function
        | NewValue.RealApprox a -> Trig.Acsch a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Acsch a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> acsch
        | NewValue.Constant c -> resolveConstant c |> acsch
        | NewValue.PositiveInfinity -> zero
        | NewValue.NegativeInfinity -> zero
        | NewValue.ComplexInfinity -> zero
        | NewValue.Undefined -> NewValue.Undefined

    let rec asech = function
        | NewValue.RealApprox a -> Trig.Asech a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Asech a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> asech
        | NewValue.Constant c -> resolveConstant c |> asech
        | NewValue.PositiveInfinity -> NewValue.ComplexApprox (complex 0.0 Constants.PiOver2)
        | NewValue.NegativeInfinity -> NewValue.ComplexApprox (complex 0.0 -Constants.PiOver2)
        | NewValue.Undefined | NewValue.ComplexInfinity -> NewValue.Undefined

    let rec acoth = function
        | NewValue.RealApprox a -> Trig.Acoth a |> fromReal
        | NewValue.ComplexApprox a -> Trig.Acoth a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> acoth
        | NewValue.Constant c -> resolveConstant c |> acoth
        | NewValue.PositiveInfinity -> zero
        | NewValue.NegativeInfinity -> zero
        | NewValue.ComplexInfinity -> zero
        | NewValue.Undefined -> NewValue.Undefined


    let rec airyai = function
        | NewValue.RealApprox a -> SpecialFunctions.AiryAi a |> fromReal
        | NewValue.ComplexApprox a -> SpecialFunctions.AiryAi a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> airyai
        | NewValue.Constant c -> resolveConstant c |> airyai
        | NewValue.PositiveInfinity -> zero
        | NewValue.NegativeInfinity -> zero
        | NewValue.ComplexInfinity -> NewValue.Undefined
        | NewValue.Undefined -> NewValue.Undefined

    let rec airyaiprime = function
        | NewValue.RealApprox a -> SpecialFunctions.AiryAiPrime a |> fromReal
        | NewValue.ComplexApprox a -> SpecialFunctions.AiryAiPrime a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> airyaiprime
        | NewValue.Constant c -> resolveConstant c |> airyaiprime
        | NewValue.PositiveInfinity -> zero
        | NewValue.ComplexInfinity -> NewValue.Undefined
        | NewValue.Undefined -> NewValue.Undefined

    let rec airybi = function
        | NewValue.RealApprox a -> SpecialFunctions.AiryBi a |> fromReal
        | NewValue.ComplexApprox a -> SpecialFunctions.AiryBi a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> airybi
        | NewValue.Constant c -> resolveConstant c |> airybi
        | NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | NewValue.NegativeInfinity -> zero
        | NewValue.ComplexInfinity -> NewValue.Undefined
        | NewValue.Undefined -> NewValue.Undefined

    let rec airybiprime = function
        | NewValue.RealApprox a -> SpecialFunctions.AiryBiPrime a |> fromReal
        | NewValue.ComplexApprox a -> SpecialFunctions.AiryBiPrime a |> fromComplex
        | NewValue.Rational a -> NewValue.RealApprox (float a) |> airybiprime
        | NewValue.Constant c -> resolveConstant c |> airybiprime
        | NewValue.PositiveInfinity -> NewValue.PositiveInfinity
        | NewValue.NegativeInfinity -> zero
        | NewValue.ComplexInfinity -> NewValue.Undefined
        | NewValue.Undefined -> NewValue.Undefined


    let besselj nu z =
        match nu, z with
        | NewValue.RealApprox a, NewValue.RealApprox b -> SpecialFunctions.BesselJ (a, b) |> fromReal
        | NewValue.RealApprox a, NewValue.ComplexApprox b -> SpecialFunctions.BesselJ (a, b) |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b -> failwith "not supported"
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> failwith "not supported"

    let bessely nu z =
        match nu, z with
        | NewValue.RealApprox a, NewValue.RealApprox b -> SpecialFunctions.BesselY (a, b) |> fromReal
        | NewValue.RealApprox a, NewValue.ComplexApprox b -> SpecialFunctions.BesselY (a, b) |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b -> failwith "not supported"
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> failwith "not supported"

    let besseli nu z =
        match nu, z with
        | NewValue.RealApprox a, NewValue.RealApprox b -> SpecialFunctions.BesselI (a, b) |> fromReal
        | NewValue.RealApprox a, NewValue.ComplexApprox b -> SpecialFunctions.BesselI (a, b) |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b -> failwith "not supported"
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> failwith "not supported"

    let besselk nu z =
        match nu, z with
        | NewValue.RealApprox a, NewValue.RealApprox b -> SpecialFunctions.BesselK (a, b) |> fromReal
        | NewValue.RealApprox a, NewValue.ComplexApprox b -> SpecialFunctions.BesselK (a, b) |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b -> failwith "not supported"
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> failwith "not supported"

    let besseliratio nu z =
        match nu, z with
        | NewValue.RealApprox a, NewValue.RealApprox b -> SpecialFunctions.BesselIScaled (a + 1.0, b) / SpecialFunctions.BesselIScaled (a, b) |> fromReal
        | NewValue.RealApprox a, NewValue.ComplexApprox b -> SpecialFunctions.BesselIScaled (a + 1.0, b) / SpecialFunctions.BesselIScaled (a, b) |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b -> failwith "not supported"
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> failwith "not supported"

    let besselkratio nu z =
        match nu, z with
        | NewValue.RealApprox a, NewValue.RealApprox b -> SpecialFunctions.BesselKScaled (a + 1.0, b) / SpecialFunctions.BesselKScaled (a, b) |> fromReal
        | NewValue.RealApprox a, NewValue.ComplexApprox b -> SpecialFunctions.BesselKScaled (a + 1.0, b) / SpecialFunctions.BesselKScaled (a, b) |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b -> failwith "not supported"
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> failwith "not supported"

    let hankelh1 nu z =
        match nu, z with
        | NewValue.RealApprox a, NewValue.RealApprox b -> SpecialFunctions.HankelH1 (a, complex b 0.0) |> fromComplex
        | NewValue.RealApprox a, NewValue.ComplexApprox b -> SpecialFunctions.HankelH1 (a, b) |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b -> failwith "not supported"
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> failwith "not supported"

    let hankelh2 nu z =
        match nu, z with
        | NewValue.RealApprox a, NewValue.RealApprox b -> SpecialFunctions.HankelH2 (a, complex b 0.0) |> fromComplex
        | NewValue.RealApprox a, NewValue.ComplexApprox b -> SpecialFunctions.HankelH2 (a, b) |> fromComplex
        | NewValue.ComplexApprox a, NewValue.RealApprox b -> failwith "not supported"
        | NewValue.ComplexApprox a, NewValue.ComplexApprox b -> failwith "not supported"

    let apply f a =
        match f with
        | Abs -> abs a
        | Ln -> ln a
        | Log -> log10 a
        | Exp -> exp a
        | Sin ->sin a
        | Cos -> cos a
        | Tan -> tan a
        | Csc -> csc a
        | Sec -> sec a
        | Cot -> cot a
        | Sinh -> sinh a
        | Cosh-> cosh a
        | Tanh -> tanh a
        | Csch -> csch a
        | Sech -> sech a
        | Coth -> coth a
        | Asin -> asin a
        | Acos -> acos a
        | Atan -> atan a
        | Acsc -> acsc a
        | Asec -> asec a
        | Acot -> acot a
        | Asinh -> asinh a
        | Acosh -> acosh a
        | Atanh -> atanh a
        | Acsch -> acsch a
        | Asech -> asech a
        | Acoth -> acoth a
        | AiryAi -> airyai a
        | AiryAiPrime -> airyaiprime a
        | AiryBi -> airybi a
        | AiryBiPrime -> airybiprime a
        | _ -> failwith "not supported"

    let applyN f xs =
        match f, xs with
        | Atan, [x; y] -> atan2 x y
        | Log, [b; x] -> log b x
        | BesselJ, [nu; x] -> besselj nu x
        | BesselY, [nu; x] -> bessely nu x
        | BesselI, [nu; x] -> besseli nu x
        | BesselK, [nu; x] -> besselk nu x
        | BesselIRatio, [nu; x] -> besseliratio nu x
        | BesselKRatio, [nu; x] -> besselkratio nu x
        | HankelH1, [nu; x] -> hankelh1 nu x
        | HankelH2, [nu; x] -> hankelh2 nu x
        | _ -> failwith "not supported"


//type NewValue with

    //static member op_Implicit (x:int) = NewValue.fromInt32 x
    //static member op_Implicit (x:int64) = NewValue.fromInt64 x
    //static member op_Implicit (x:BigInteger) = NewValue.fromInteger x
    //static member op_Implicit (x:BigRational) = NewValue.fromRational x
    //static member op_Implicit (x:float) = NewValue.fromReal x
    //static member op_Implicit (x:float32) = NewValue.fromReal32 x
    //static member op_Implicit (x:complex) = NewValue.fromComplex x
    //static member op_Implicit (x:complex32) = NewValue.fromComplex32 x
