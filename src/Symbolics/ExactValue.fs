namespace MathNet.Symbolics

open System
open MathNet.Numerics
open MathNet.Symbolics

type BigInteger = System.Numerics.BigInteger

type ComplexBigRational = {
    Real: BigRational
    Imaginary: BigRational
}

[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module ComplexBigRational =
    let (|RealRational|_|) ({ ComplexBigRational.Real=real; Imaginary=imag }) : BigRational option = if imag.IsZero then Some real else None
    let (|RealInteger|_|) ({ ComplexBigRational.Real=real; Imaginary=imag }) : BigInteger option = if imag.IsZero && real.IsInteger then Some real.Numerator else None
    let (|Complex|) ({ ComplexBigRational.Real=real; Imaginary=imag }) : BigRational * BigRational = (real, imag)


[<RequireQualifiedAccess>]
module internal FromPrimitive =
    let inline complex32 (x:complex32) = complex (float x.Real) (float x.Imaginary)
    let inline int32 (x:int) = BigRational.FromInt x
    let inline int64 (x:int64) = BigRational.FromBigInt (BigInteger x)
    let inline bigint (x:BigInteger) = BigRational.FromBigInt x

[<RequireQualifiedAccess>]
type ExactValue =
    | Rational of BigRational
    | ComplexRational of ComplexBigRational
    | Constant of Constant
    | DirectedConstant of Constant * ComplexBigRational
    | ComplexInfinity
    | PositiveInfinity
    | NegativeInfinity
    | DirectedInfinity of ComplexBigRational
    | Undefined

[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module ExactValue =

    let zero = ExactValue.Rational BigRational.Zero
    let one = ExactValue.Rational BigRational.One
    let minusOne = ExactValue.Rational (BigRational.FromInt -1)
    let imagOne = ExactValue.ComplexRational { ComplexBigRational.Real = BigRational.Zero; Imaginary = BigRational.One }
    let imagMinusOne = ExactValue.ComplexRational { ComplexBigRational.Real = BigRational.Zero; Imaginary = -BigRational.One }

    let fromInt32 (x:int) = ExactValue.Rational (FromPrimitive.int32 x)
    let fromInt64 (x:int64) = ExactValue.Rational (FromPrimitive.int64 x)
    let fromInteger (x:BigInteger) = ExactValue.Rational (FromPrimitive.bigint x)
    let fromIntegerFraction (n:BigInteger) (d:BigInteger) = ExactValue.Rational (BigRational.FromBigIntFraction (n, d))
    let fromRational (x:BigRational) = ExactValue.Rational x
    let fromComplexInt32 (real:int) (imag:int) =
        if imag = 0 then fromInt32 real
        else ExactValue.ComplexRational { ComplexBigRational.Real = FromPrimitive.int32 real; Imaginary = FromPrimitive.int32 imag }
    let fromComplexInt64 (real:int64) (imag:int64) =
        if imag = 0L then fromInt64 real
        else ExactValue.ComplexRational { ComplexBigRational.Real = FromPrimitive.int64 real; Imaginary = FromPrimitive.int64 imag }
    let fromComplexInteger (real:BigInteger) (imag:BigInteger) =
        if imag.IsZero then fromInteger real
        else ExactValue.ComplexRational { ComplexBigRational.Real = FromPrimitive.bigint real; Imaginary = FromPrimitive.bigint imag }
    let fromComplexRational (real:BigRational) (imag:BigRational) =
        if imag.IsZero then fromRational real
        else ExactValue.ComplexRational { ComplexBigRational.Real = real; Imaginary = imag }
    let fromConstant (c:Constant) =
        match c with
        | I -> imagOne
        | constant -> ExactValue.Constant constant
    let fromConstantDirectedInt32 (c:Constant) (real:int) (imag:int) =
        if c = I then fromComplexInt32 -imag real else
        match real, imag with
        | 0, 0 -> zero
        | 1, 0 -> fromConstant c
        | r, i -> ExactValue.DirectedConstant (c, { ComplexBigRational.Real = FromPrimitive.int32 r; Imaginary = FromPrimitive.int32 i })
    let fromConstantDirectedInteger (c:Constant) (real:BigInteger) (imag:BigInteger) =
        if c = I then fromComplexInteger -imag real else
        match real, imag with
        | r, i when r.IsZero && i.IsZero -> zero
        | r, i when r.IsOne && i.IsZero -> fromConstant c
        | r, i -> ExactValue.DirectedConstant (c, { ComplexBigRational.Real = FromPrimitive.bigint r; Imaginary = FromPrimitive.bigint i })
    let fromConstantDirectedRational (c:Constant) (real:BigRational) (imag:BigRational) =
        if c = I then fromComplexRational -imag real else
        match real, imag with
        | r, i when r.IsZero && i.IsZero -> zero
        | r, i when r.IsOne && i.IsZero -> fromConstant c
        | r, i -> ExactValue.DirectedConstant (c, { ComplexBigRational.Real = r; Imaginary = i })
    let fromInfinityDirectedInt32 (real:int) (imag:int) =
        match real, imag with
        | 0, 0 -> ExactValue.Undefined
        | 1, 0 -> ExactValue.PositiveInfinity
        | -1, 0 -> ExactValue.NegativeInfinity
        | r, i -> ExactValue.DirectedInfinity { ComplexBigRational.Real = FromPrimitive.int32 r; Imaginary = FromPrimitive.int32 i }
    let fromInfinityDirectedInteger (real:BigInteger) (imag:BigInteger) =
        match real, imag with
        | r, i when r.IsZero && i.IsZero -> ExactValue.Undefined
        | r, i when r.IsOne && i.IsZero -> ExactValue.PositiveInfinity
        | r, i when r = BigInteger.MinusOne && i.IsZero -> ExactValue.NegativeInfinity
        | r, i -> ExactValue.DirectedInfinity { ComplexBigRational.Real = FromPrimitive.bigint r; Imaginary = FromPrimitive.bigint i }
    let fromInfinityDirectedRational (real:BigRational) (imag:BigRational) =
        match real, imag with
        | r, i when r.IsZero && i.IsZero -> ExactValue.Undefined
        | r, i when r.IsOne && i.IsZero -> ExactValue.PositiveInfinity
        | r, i when r.IsInteger && r.Numerator = BigInteger.MinusOne && i.IsZero -> ExactValue.NegativeInfinity
        | r, i -> ExactValue.DirectedInfinity { ComplexBigRational.Real = r; Imaginary = i }

    let (|Zero|_|) = function
        | ExactValue.Rational n when n.IsZero -> Some Zero
        | ExactValue.ComplexRational x when x.Real.IsZero && x.Imaginary.IsZero -> Some Zero
        | _ -> None

    let (|One|_|) = function
        | ExactValue.Rational n when n.IsOne -> Some One
        | ExactValue.ComplexRational n when n.Real.IsOne && n.Imaginary.IsZero -> Some One
        | _ -> None

    let (|MinusOne|_|) = function
        | ExactValue.Rational n when n.IsInteger && n.Numerator = BigInteger.MinusOne -> Some MinusOne
        | ExactValue.ComplexRational n when n.Real.IsInteger && n.Real.Numerator = BigInteger.MinusOne && n.Imaginary.IsZero -> Some MinusOne
        | _ -> None

    let (|Positive|_|) = function
        | ExactValue.Rational n when n.IsPositive -> Some Positive
        | ExactValue.ComplexRational n when n.Real.IsPositive && n.Imaginary.IsZero -> Some Positive
        | ExactValue.PositiveInfinity -> Some Positive
        | ExactValue.Constant E | ExactValue.Constant Pi -> Some Positive
        | _ -> None

    let (|Negative|_|) = function
        | ExactValue.Rational n when n.IsNegative -> Some Negative
        | ExactValue.ComplexRational n when n.Real.IsNegative && n.Imaginary.IsZero -> Some Negative
        | ExactValue.NegativeInfinity -> Some Negative
        | _ -> None

    let isZero = function | Zero -> true | _ -> false
    let isOne = function | One -> true | _ -> false
    let isMinusOne = function | MinusOne -> true | _ -> false
    let isPositive = function | Positive -> true | _ -> false
    let isNegative = function | Negative -> true | _ -> false

    let negate = function
        | ExactValue.Rational a -> ExactValue.Rational (-a)
        | ExactValue.ComplexRational a -> fromComplexRational (-a.Real) (-a.Imaginary)
        | ExactValue.Constant c -> fromConstantDirectedInt32 c -1 0
        | ExactValue.DirectedConstant (c, d) -> fromConstantDirectedRational c (-d.Real) (-d.Imaginary)
        | ExactValue.NegativeInfinity -> ExactValue.PositiveInfinity
        | ExactValue.PositiveInfinity -> ExactValue.NegativeInfinity
        | ExactValue.ComplexInfinity -> ExactValue.ComplexInfinity
        | ExactValue.DirectedInfinity d -> fromInfinityDirectedRational (-d.Real) (-d.Imaginary)
        | ExactValue.Undefined -> ExactValue.Undefined

    let tryAbs = function
        | Zero | Positive as x -> Some x
        | ExactValue.Rational a -> fromRational (BigRational.Abs a) |> Some
        | ExactValue.ComplexRational a ->
            match a.Real, a.Imaginary with
            | r, i when r.IsZero -> fromRational (BigRational.Abs i) |> Some
            | r, i when i.IsZero -> fromRational (BigRational.Abs r) |> Some
            | _ -> None
        | ExactValue.Constant I -> Some one
        | ExactValue.Constant _ as positiveReal -> Some positiveReal
        | ExactValue.DirectedConstant (c, d) -> None // TODO
        | ExactValue.NegativeInfinity -> Some ExactValue.PositiveInfinity
        | ExactValue.PositiveInfinity -> Some ExactValue.PositiveInfinity
        | ExactValue.DirectedInfinity _ -> Some ExactValue.PositiveInfinity
        | ExactValue.ComplexInfinity -> Some ExactValue.PositiveInfinity
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let trySum = function
        | ExactValue.Undefined, _ | _, ExactValue.Undefined -> Some ExactValue.Undefined
        | Zero, b | b, Zero -> Some b
        | ExactValue.Rational a, ExactValue.Rational b -> fromRational (a + b) |> Some
        | ExactValue.ComplexRational a, ExactValue.ComplexRational b -> fromComplexRational (a.Real + b.Real) (a.Imaginary + b.Imaginary) |> Some
        | ExactValue.Rational a, ExactValue.ComplexRational b | ExactValue.ComplexRational b, ExactValue.Rational a -> fromComplexRational (a + b.Real) b.Imaginary |> Some
        | ExactValue.Constant a, ExactValue.Constant b when a = b -> fromConstantDirectedInt32 a 2 0 |> Some
        | ExactValue.DirectedConstant (a,da), ExactValue.DirectedConstant (b,db) when a = b -> fromConstantDirectedRational a (da.Real + db.Real) (da.Imaginary + db.Imaginary) |> Some
        | ExactValue.Constant a, ExactValue.DirectedConstant (b, d) | ExactValue.DirectedConstant (b, d), ExactValue.Constant a when a = b -> fromConstantDirectedRational a (d.Real + BigRational.One) d.Imaginary |> Some
        | ExactValue.ComplexInfinity, (ExactValue.ComplexInfinity | ExactValue.PositiveInfinity | ExactValue.NegativeInfinity | ExactValue.DirectedInfinity _) -> Some ExactValue.Undefined
        | (ExactValue.ComplexInfinity | ExactValue.PositiveInfinity | ExactValue.NegativeInfinity | ExactValue.DirectedInfinity _),  ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.ComplexInfinity, _ | _, ExactValue.ComplexInfinity -> Some ExactValue.ComplexInfinity
        | ExactValue.PositiveInfinity, ExactValue.PositiveInfinity -> Some ExactValue.PositiveInfinity
        | ExactValue.PositiveInfinity, ExactValue.NegativeInfinity | ExactValue.NegativeInfinity, ExactValue.PositiveInfinity -> Some ExactValue.Undefined
        | ExactValue.PositiveInfinity, ExactValue.DirectedInfinity _ | ExactValue.DirectedInfinity _, ExactValue.PositiveInfinity -> Some ExactValue.Undefined
        | ExactValue.PositiveInfinity, _ | _, ExactValue.PositiveInfinity -> Some ExactValue.PositiveInfinity
        | ExactValue.NegativeInfinity, ExactValue.NegativeInfinity -> Some ExactValue.NegativeInfinity
        | ExactValue.NegativeInfinity, ExactValue.DirectedInfinity _ | ExactValue.DirectedInfinity _, ExactValue.NegativeInfinity -> Some ExactValue.Undefined
        | ExactValue.NegativeInfinity, _ | _, ExactValue.NegativeInfinity -> Some ExactValue.NegativeInfinity
        | ExactValue.DirectedInfinity a, ExactValue.DirectedInfinity b when a = b -> Some (ExactValue.DirectedInfinity a)
        | ExactValue.DirectedInfinity a, ExactValue.DirectedInfinity b -> fromInfinityDirectedRational (a.Real + b.Real) (a.Imaginary + b.Imaginary) |> Some
        | ExactValue.DirectedInfinity d, _ | _, ExactValue.DirectedInfinity d -> Some (ExactValue.DirectedInfinity d)
        | ExactValue.Constant _, _ | _, ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant _, _ | _, ExactValue.DirectedConstant _ -> None
        
    let tryProduct = function
        | ExactValue.Undefined, _ | _, ExactValue.Undefined -> Some ExactValue.Undefined
        | One, b | b, One -> Some b
        | Zero, (ExactValue.ComplexInfinity | ExactValue.PositiveInfinity | ExactValue.NegativeInfinity | ExactValue.DirectedInfinity _) -> Some ExactValue.Undefined
        | (ExactValue.ComplexInfinity | ExactValue.PositiveInfinity | ExactValue.NegativeInfinity | ExactValue.DirectedInfinity _), Zero -> Some ExactValue.Undefined
        | Zero, _ | _, Zero -> Some zero
        | ExactValue.Rational a, ExactValue.Rational b -> fromRational (a * b) |> Some
        | ExactValue.ComplexRational a, ExactValue.ComplexRational b -> fromComplexRational (a.Real * b.Real - a.Imaginary * b.Imaginary) (a.Real * b.Imaginary + a.Imaginary * b.Real) |> Some
        | ExactValue.Rational a, ExactValue.ComplexRational b | ExactValue.ComplexRational b, ExactValue.Rational a -> fromComplexRational (a * b.Real) (a * b.Imaginary) |> Some
        | ExactValue.Constant a, ExactValue.Rational b | ExactValue.Rational b, ExactValue.Constant a -> fromConstantDirectedRational a b BigRational.Zero |> Some
        | ExactValue.Constant a, ExactValue.ComplexRational b | ExactValue.ComplexRational b, ExactValue.Constant a -> fromConstantDirectedRational a b.Real b.Imaginary |> Some
        | ExactValue.DirectedConstant (a,d), ExactValue.Rational b | ExactValue.Rational b, ExactValue.DirectedConstant (a,d) -> fromConstantDirectedRational a (b * d.Real) (b * d.Imaginary) |> Some
        | ExactValue.DirectedConstant (a,d), ExactValue.ComplexRational b | ExactValue.ComplexRational b, ExactValue.DirectedConstant (a,d) -> fromConstantDirectedRational a (b.Real * d.Real - b.Imaginary * d.Imaginary) (b.Real * d.Imaginary + b.Imaginary * d.Real)|> Some
        | ExactValue.ComplexInfinity, _ | _, ExactValue.ComplexInfinity -> Some ExactValue.ComplexInfinity
        | ExactValue.PositiveInfinity, Positive | Positive, ExactValue.PositiveInfinity -> Some ExactValue.PositiveInfinity
        | ExactValue.PositiveInfinity, Negative | Negative, ExactValue.PositiveInfinity -> Some ExactValue.NegativeInfinity
        | ExactValue.NegativeInfinity, Positive | Positive, ExactValue.NegativeInfinity -> Some ExactValue.NegativeInfinity
        | ExactValue.NegativeInfinity, Negative | Negative, ExactValue.NegativeInfinity -> Some ExactValue.PositiveInfinity
        | ExactValue.DirectedInfinity d, Positive | Positive, ExactValue.DirectedInfinity d -> Some (ExactValue.DirectedInfinity d)
        | ExactValue.DirectedInfinity d, Negative | Negative, ExactValue.DirectedInfinity d -> fromInfinityDirectedRational (-d.Real) (-d.Imaginary) |> Some
        | ExactValue.NegativeInfinity, _ | _, ExactValue.NegativeInfinity -> Some ExactValue.NegativeInfinity
        | ExactValue.PositiveInfinity, _ | _, ExactValue.PositiveInfinity -> Some ExactValue.PositiveInfinity
        | ExactValue.DirectedInfinity d, _ | _, ExactValue.DirectedInfinity d -> Some (ExactValue.DirectedInfinity d)
        | ExactValue.Constant _, _ | _, ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant _, _ | _, ExactValue.DirectedConstant _ -> None
        
        //| ExactValue.Rational a -> ExactValue.Rational a
        //| ExactValue.ComplexRational a -> fromComplexRational a.Real a.Imaginary
        //| ExactValue.Constant c -> fromConstantDirectedInt32 c 1 0
        //| ExactValue.DirectedConstant (c, d) -> fromConstantDirectedRational c d.Real d.Imaginary
        //| ExactValue.NegativeInfinity -> ExactValue.NegativeInfinity
        //| ExactValue.PositiveInfinity -> ExactValue.PositiveInfinity
        //| ExactValue.DirectedInfinity d -> fromInfinityDirectedRational d.Real d.Imaginary
        //| ExactValue.ComplexInfinity -> ExactValue.ComplexInfinity
        //| ExactValue.Undefined -> ExactValue.Undefined

    let tryInvert = function
        | Zero -> Some ExactValue.ComplexInfinity
        | ExactValue.Rational a -> fromRational (BigRational.Reciprocal a) |> Some
        | ExactValue.ComplexRational a ->
            let denominator = a.Real*a.Real + a.Imaginary*a.Imaginary
            fromComplexRational (a.Real/denominator) (-a.Imaginary/denominator) |> Some
        | ExactValue.Constant I -> Some imagMinusOne
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.ComplexInfinity | ExactValue.PositiveInfinity | ExactValue.NegativeInfinity | ExactValue.DirectedInfinity _ -> Some zero
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let rec power = function
        | ExactValue.Undefined, _ | _, ExactValue.Undefined -> ExactValue.Undefined
        | Zero, Zero -> ExactValue.Undefined
        | Zero, (ExactValue.ComplexInfinity | ExactValue.PositiveInfinity) -> zero
        | Zero, ExactValue.NegativeInfinity -> ExactValue.ComplexInfinity
        | Zero, Positive -> zero
        | Zero, Negative -> ExactValue.ComplexInfinity
        | (ExactValue.ComplexInfinity | ExactValue.PositiveInfinity | ExactValue.NegativeInfinity), Zero -> ExactValue.Undefined
        | (ExactValue.ComplexInfinity | ExactValue.PositiveInfinity | ExactValue.NegativeInfinity), ExactValue.PositiveInfinity -> ExactValue.ComplexInfinity
        | (ExactValue.ComplexInfinity | ExactValue.PositiveInfinity | ExactValue.NegativeInfinity), ExactValue.Rational b when b.IsNegative -> zero
        | ExactValue.ComplexInfinity, Positive -> ExactValue.ComplexInfinity
        | ExactValue.PositiveInfinity, Positive -> ExactValue.PositiveInfinity
        | ExactValue.NegativeInfinity, ExactValue.Rational b when b.IsPositive && b.IsInteger ->
            if (b.Numerator % 2I).IsZero then ExactValue.PositiveInfinity else ExactValue.NegativeInfinity
        | One, (ExactValue.ComplexInfinity | ExactValue.PositiveInfinity | ExactValue.NegativeInfinity) | MinusOne, (ExactValue.ComplexInfinity | ExactValue.PositiveInfinity | ExactValue.NegativeInfinity) -> ExactValue.Undefined
        | One, _ | _, Zero -> one
        | _, Zero -> one
        | a, One -> a
        | One, _ -> one
        | Positive, ExactValue.PositiveInfinity -> ExactValue.PositiveInfinity
        | Negative, ExactValue.PositiveInfinity -> ExactValue.ComplexInfinity
        | _, ExactValue.NegativeInfinity -> zero
        | _, ExactValue.ComplexInfinity -> ExactValue.Undefined
        | ExactValue.Rational a, ExactValue.Rational b when b.IsInteger ->
            if b.IsNegative then
                if a.IsZero then ExactValue.ComplexInfinity
                // workaround bug in BigRational with negative powers - drop after upgrading to > v3.0.0-alpha9
                else ExactValue.Rational (BigRational.Pow(BigRational.Reciprocal a, -int(b.Numerator)))
            else ExactValue.Rational (BigRational.Pow(a, int(b.Numerator)))
        | ExactValue.RealApprox a, ExactValue.RealApprox b -> a**b |> fromReal
        | ExactValue.ComplexApprox a, ExactValue.ComplexApprox b -> Complex.pow b a |> fromComplex
        | ExactValue.RealApprox a, ExactValue.ComplexApprox b -> Complex.pow b (complex a 0.0) |> fromComplex
        | ExactValue.ComplexApprox a, ExactValue.RealApprox b -> Complex.pow (complex b 0.0) a |> fromComplex
        | ExactValue.Rational a, ExactValue.Rational b -> (float a)**(float b) |> fromReal // TODO: must be a better way
        | ExactValue.RealApprox a, ExactValue.Rational b -> a**(float b) |> fromReal
        | ExactValue.ComplexApprox a, ExactValue.Rational b -> Complex.pow (complex (float b) 0.0) a |> fromComplex
        | ExactValue.Rational a, ExactValue.RealApprox b -> (float a)**b |> fromReal
        | ExactValue.Rational a, ExactValue.ComplexApprox b -> Complex.pow b (complex (float a) 0.0) |> fromComplex
        | ExactValue.Constant a, b -> power (resolveConstant a, b)
        | a, ExactValue.Constant b -> power (a, resolveConstant b)
        | _ -> ExactValue.Undefined // TODO

    let rec ln = function
        | Zero -> ExactValue.NegativeInfinity
        | One -> zero
        | ExactValue.Constant E -> one
        | ExactValue.RealApprox a -> Math.Log a |> fromReal
        | ExactValue.ComplexApprox a -> Complex.ln a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> ln
        | ExactValue.Constant c -> resolveConstant c |> ln
        | ExactValue.ComplexInfinity -> ExactValue.PositiveInfinity
        | ExactValue.PositiveInfinity -> ExactValue.PositiveInfinity
        | ExactValue.NegativeInfinity -> ExactValue.PositiveInfinity
        | ExactValue.Undefined -> ExactValue.Undefined

    let rec log10 = function
        | Zero -> ExactValue.NegativeInfinity
        | One -> zero
        | ExactValue.Rational n when n.Equals(10N) -> one
        | ExactValue.RealApprox a -> Math.Log10 a |> fromReal
        | ExactValue.ComplexApprox a -> Complex.log10 a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> log10
        | ExactValue.Constant c -> resolveConstant c |> log10
        | ExactValue.ComplexInfinity -> ExactValue.PositiveInfinity
        | ExactValue.PositiveInfinity -> ExactValue.PositiveInfinity
        | ExactValue.NegativeInfinity -> ExactValue.PositiveInfinity
        | ExactValue.Undefined -> ExactValue.Undefined

    let log b x =
        match b, x with
        | ExactValue.RealApprox v, ExactValue.RealApprox w -> Math.Log (v, w) |> fromReal
        | ExactValue.RealApprox v, ExactValue.ComplexApprox w -> Complex.log v w |> fromComplex
        | _ -> failwith "not supported"

    let rec exp = function
        | Zero -> one
        | One -> ExactValue.Constant E
        | MinusOne -> ExactValue.Constant E |> invert
        | ExactValue.RealApprox a -> Math.Exp a |> fromReal
        | ExactValue.ComplexApprox a -> Complex.exp a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> log10
        | ExactValue.Constant c -> resolveConstant c |> log10
        | ExactValue.ComplexInfinity -> ExactValue.Undefined
        | ExactValue.PositiveInfinity -> ExactValue.PositiveInfinity
        | ExactValue.NegativeInfinity -> zero
        | ExactValue.Undefined -> ExactValue.Undefined


    let trySin = function
        | Zero -> Some zero
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant Pi -> Some zero
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant (Pi, ComplexBigRational.RealInteger _) -> Some zero // sin(n*pi) = 0 for integer n
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some ExactValue.Undefined
        | ExactValue.NegativeInfinity -> Some ExactValue.Undefined
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let tryCos = function
        | Zero -> Some one
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant Pi -> Some minusOne
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant (Pi, ComplexBigRational.RealInteger n) -> if n.IsEven then Some one else Some minusOne
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some ExactValue.Undefined
        | ExactValue.NegativeInfinity -> Some ExactValue.Undefined
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let tryTan = function
        | Zero -> Some zero
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant Pi -> Some zero
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant (Pi, ComplexBigRational.RealInteger _) -> Some zero // tan(n*pi) = 0 for integer n
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some ExactValue.Undefined
        | ExactValue.NegativeInfinity -> Some ExactValue.Undefined
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let tryCsc = function
        | Zero -> Some ExactValue.ComplexInfinity
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant Pi -> Some ExactValue.ComplexInfinity
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant (Pi, ComplexBigRational.RealInteger _) -> Some ExactValue.ComplexInfinity
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some ExactValue.Undefined
        | ExactValue.NegativeInfinity -> Some ExactValue.Undefined
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let trySec = function
        | Zero -> Some one
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant Pi -> Some minusOne
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant (Pi, ComplexBigRational.RealInteger n) -> if n.IsEven then Some one else Some minusOne
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some ExactValue.Undefined
        | ExactValue.NegativeInfinity -> Some ExactValue.Undefined
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let tryCot = function
        | Zero -> Some ExactValue.ComplexInfinity
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant Pi -> Some ExactValue.ComplexInfinity
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant (Pi, ComplexBigRational.RealInteger _) -> Some ExactValue.ComplexInfinity
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some ExactValue.Undefined
        | ExactValue.NegativeInfinity -> Some ExactValue.Undefined
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined


    let trySinh = function
        | Zero -> Some zero
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some ExactValue.PositiveInfinity
        | ExactValue.NegativeInfinity -> Some ExactValue.NegativeInfinity
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined // TODO
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let tryCosh = function
        | Zero -> Some one
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some ExactValue.PositiveInfinity
        | ExactValue.NegativeInfinity -> Some ExactValue.PositiveInfinity
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined // TODO
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let tryTanh = function
        | Zero -> Some zero
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some one
        | ExactValue.NegativeInfinity -> Some minusOne
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined // TODO
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let tryCsch = function
        | Zero -> Some ExactValue.ComplexInfinity
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some zero
        | ExactValue.NegativeInfinity -> Some zero
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined // TODO
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let trySech = function
        | Zero -> Some one
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some zero
        | ExactValue.NegativeInfinity -> Some zero
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined // TODO
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined

    let tryCoth = function
        | Zero -> Some ExactValue.ComplexInfinity
        | ExactValue.Rational _ -> None
        | ExactValue.ComplexRational _ -> None
        | ExactValue.Constant _ -> None
        | ExactValue.DirectedConstant _ -> None
        | ExactValue.PositiveInfinity -> Some one
        | ExactValue.NegativeInfinity -> Some minusOne
        | ExactValue.DirectedInfinity _ -> Some ExactValue.Undefined // TODO
        | ExactValue.ComplexInfinity -> Some ExactValue.Undefined
        | ExactValue.Undefined -> Some ExactValue.Undefined
        
        
        //| ExactValue.Rational a -> ExactValue.Rational a
        //| ExactValue.ComplexRational a -> fromComplexRational a.Real a.Imaginary
        //| ExactValue.Constant c -> fromConstantDirectedInt32 c 1 0
        //| ExactValue.DirectedConstant (c, d) -> fromConstantDirectedRational c d.Real d.Imaginary
        //| ExactValue.NegativeInfinity -> ExactValue.NegativeInfinity
        //| ExactValue.PositiveInfinity -> ExactValue.PositiveInfinity
        //| ExactValue.DirectedInfinity d -> fromInfinityDirectedRational d.Real d.Imaginary
        //| ExactValue.ComplexInfinity -> ExactValue.ComplexInfinity
        //| ExactValue.Undefined -> ExactValue.Undefined

    let rec asin = function
        | Zero -> zero
        | ExactValue.RealApprox a -> Trig.Asin a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Asin a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> asin
        | ExactValue.Constant c -> resolveConstant c |> asin
        | ExactValue.PositiveInfinity -> ExactValue.ComplexInfinity // actually: i*oo
        | ExactValue.NegativeInfinity -> ExactValue.ComplexInfinity // actually: -i*oo
        | ExactValue.ComplexInfinity -> ExactValue.ComplexInfinity
        | ExactValue.Undefined -> ExactValue.Undefined

    let rec acos = function
        | One -> zero
        | MinusOne -> ExactValue.Constant Constant.Pi
        | ExactValue.RealApprox a -> Trig.Acos a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Acos a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> acos
        | ExactValue.Constant c -> resolveConstant c |> acos
        | ExactValue.PositiveInfinity -> ExactValue.ComplexInfinity // actually: -i*oo
        | ExactValue.NegativeInfinity -> ExactValue.ComplexInfinity // actually: i*oo
        | ExactValue.ComplexInfinity -> ExactValue.ComplexInfinity
        | ExactValue.Undefined -> ExactValue.Undefined

    let rec atan = function
        | Zero -> zero
        | ExactValue.RealApprox a -> Trig.Atan a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Atan a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> atan
        | ExactValue.Constant c -> resolveConstant c |> atan
        | ExactValue.PositiveInfinity -> ExactValue.RealApprox (Constants.PiOver2)
        | ExactValue.NegativeInfinity -> ExactValue.RealApprox (-Constants.PiOver2)
        | ExactValue.Undefined | ExactValue.ComplexInfinity -> ExactValue.Undefined

    let atan2 x y =
        match x, y with
        | ExactValue.RealApprox a, ExactValue.RealApprox b -> Math.Atan2 (a, b) |> fromReal
        | ExactValue.ComplexApprox a, ExactValue.ComplexApprox b -> Complex.atan (a / b) |> fromComplex
        | ExactValue.ComplexApprox a, ExactValue.RealApprox b -> Complex.atan (a / (complex b 0.0)) |> fromComplex
        | ExactValue.RealApprox a, ExactValue.ComplexApprox b -> Complex.atan (complex a 0.0) / b |> fromComplex

    let rec acsc = function
        | Zero -> ExactValue.ComplexInfinity
        | ExactValue.RealApprox a -> Trig.Acsc a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Acsc a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> acsc
        | ExactValue.Constant c -> resolveConstant c |> acsc
        | ExactValue.PositiveInfinity -> zero
        | ExactValue.NegativeInfinity -> zero
        | ExactValue.ComplexInfinity -> zero
        | ExactValue.Undefined -> ExactValue.Undefined

    let rec asec = function
        | Zero -> ExactValue.ComplexInfinity
        | One -> zero
        | MinusOne -> ExactValue.Constant Constant.Pi
        | ExactValue.RealApprox a -> Trig.Asec a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Asec a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> asec
        | ExactValue.Constant c -> resolveConstant c |> asec
        | ExactValue.PositiveInfinity -> ExactValue.RealApprox (Constants.PiOver2)
        | ExactValue.NegativeInfinity -> ExactValue.RealApprox (Constants.PiOver2)
        | ExactValue.ComplexInfinity -> ExactValue.RealApprox (Constants.PiOver2)
        | ExactValue.Undefined -> ExactValue.Undefined

    let rec acot = function
        | ExactValue.RealApprox a -> Trig.Acot a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Acot a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> acot
        | ExactValue.Constant c -> resolveConstant c |> acot
        | ExactValue.PositiveInfinity -> zero
        | ExactValue.NegativeInfinity -> zero
        | ExactValue.ComplexInfinity -> zero
        | ExactValue.Undefined -> ExactValue.Undefined


    let rec asinh = function
        | ExactValue.RealApprox a -> Trig.Asinh a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Asinh a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> asinh
        | ExactValue.Constant c -> resolveConstant c |> asinh
        | ExactValue.PositiveInfinity -> ExactValue.PositiveInfinity
        | ExactValue.NegativeInfinity -> ExactValue.NegativeInfinity
        | ExactValue.ComplexInfinity -> ExactValue.ComplexInfinity
        | ExactValue.Undefined -> ExactValue.Undefined

    let rec acosh = function
        | ExactValue.RealApprox a -> Trig.Acosh a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Acosh a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> acosh
        | ExactValue.Constant c -> resolveConstant c |> acosh
        | ExactValue.PositiveInfinity -> ExactValue.PositiveInfinity
        | ExactValue.NegativeInfinity -> ExactValue.PositiveInfinity
        | ExactValue.ComplexInfinity -> ExactValue.PositiveInfinity
        | ExactValue.Undefined -> ExactValue.Undefined

    let rec atanh = function
        | ExactValue.RealApprox a -> Trig.Atanh a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Atanh a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> atanh
        | ExactValue.Constant c -> resolveConstant c |> atanh
        | ExactValue.PositiveInfinity -> ExactValue.ComplexApprox (complex 0.0 -Constants.PiOver2)
        | ExactValue.NegativeInfinity -> ExactValue.ComplexApprox (complex 0.0 Constants.PiOver2)
        | ExactValue.Undefined | ExactValue.ComplexInfinity -> ExactValue.Undefined

    let rec acsch = function
        | ExactValue.RealApprox a -> Trig.Acsch a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Acsch a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> acsch
        | ExactValue.Constant c -> resolveConstant c |> acsch
        | ExactValue.PositiveInfinity -> zero
        | ExactValue.NegativeInfinity -> zero
        | ExactValue.ComplexInfinity -> zero
        | ExactValue.Undefined -> ExactValue.Undefined

    let rec asech = function
        | ExactValue.RealApprox a -> Trig.Asech a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Asech a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> asech
        | ExactValue.Constant c -> resolveConstant c |> asech
        | ExactValue.PositiveInfinity -> ExactValue.ComplexApprox (complex 0.0 Constants.PiOver2)
        | ExactValue.NegativeInfinity -> ExactValue.ComplexApprox (complex 0.0 -Constants.PiOver2)
        | ExactValue.Undefined | ExactValue.ComplexInfinity -> ExactValue.Undefined

    let rec acoth = function
        | ExactValue.RealApprox a -> Trig.Acoth a |> fromReal
        | ExactValue.ComplexApprox a -> Trig.Acoth a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> acoth
        | ExactValue.Constant c -> resolveConstant c |> acoth
        | ExactValue.PositiveInfinity -> zero
        | ExactValue.NegativeInfinity -> zero
        | ExactValue.ComplexInfinity -> zero
        | ExactValue.Undefined -> ExactValue.Undefined


    let rec airyai = function
        | ExactValue.RealApprox a -> SpecialFunctions.AiryAi a |> fromReal
        | ExactValue.ComplexApprox a -> SpecialFunctions.AiryAi a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> airyai
        | ExactValue.Constant c -> resolveConstant c |> airyai
        | ExactValue.PositiveInfinity -> zero
        | ExactValue.NegativeInfinity -> zero
        | ExactValue.ComplexInfinity -> ExactValue.Undefined
        | ExactValue.Undefined -> ExactValue.Undefined

    let rec airyaiprime = function
        | ExactValue.RealApprox a -> SpecialFunctions.AiryAiPrime a |> fromReal
        | ExactValue.ComplexApprox a -> SpecialFunctions.AiryAiPrime a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> airyaiprime
        | ExactValue.Constant c -> resolveConstant c |> airyaiprime
        | ExactValue.PositiveInfinity -> zero
        | ExactValue.ComplexInfinity -> ExactValue.Undefined
        | ExactValue.Undefined -> ExactValue.Undefined

    let rec airybi = function
        | ExactValue.RealApprox a -> SpecialFunctions.AiryBi a |> fromReal
        | ExactValue.ComplexApprox a -> SpecialFunctions.AiryBi a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> airybi
        | ExactValue.Constant c -> resolveConstant c |> airybi
        | ExactValue.PositiveInfinity -> ExactValue.PositiveInfinity
        | ExactValue.NegativeInfinity -> zero
        | ExactValue.ComplexInfinity -> ExactValue.Undefined
        | ExactValue.Undefined -> ExactValue.Undefined

    let rec airybiprime = function
        | ExactValue.RealApprox a -> SpecialFunctions.AiryBiPrime a |> fromReal
        | ExactValue.ComplexApprox a -> SpecialFunctions.AiryBiPrime a |> fromComplex
        | ExactValue.Rational a -> ExactValue.RealApprox (float a) |> airybiprime
        | ExactValue.Constant c -> resolveConstant c |> airybiprime
        | ExactValue.PositiveInfinity -> ExactValue.PositiveInfinity
        | ExactValue.NegativeInfinity -> zero
        | ExactValue.ComplexInfinity -> ExactValue.Undefined
        | ExactValue.Undefined -> ExactValue.Undefined


    let besselj nu z =
        match nu, z with
        | ExactValue.RealApprox a, ExactValue.RealApprox b -> SpecialFunctions.BesselJ (a, b) |> fromReal
        | ExactValue.RealApprox a, ExactValue.ComplexApprox b -> SpecialFunctions.BesselJ (a, b) |> fromComplex
        | ExactValue.ComplexApprox a, ExactValue.RealApprox b -> failwith "not supported"
        | ExactValue.ComplexApprox a, ExactValue.ComplexApprox b -> failwith "not supported"

    let bessely nu z =
        match nu, z with
        | ExactValue.RealApprox a, ExactValue.RealApprox b -> SpecialFunctions.BesselY (a, b) |> fromReal
        | ExactValue.RealApprox a, ExactValue.ComplexApprox b -> SpecialFunctions.BesselY (a, b) |> fromComplex
        | ExactValue.ComplexApprox a, ExactValue.RealApprox b -> failwith "not supported"
        | ExactValue.ComplexApprox a, ExactValue.ComplexApprox b -> failwith "not supported"

    let besseli nu z =
        match nu, z with
        | ExactValue.RealApprox a, ExactValue.RealApprox b -> SpecialFunctions.BesselI (a, b) |> fromReal
        | ExactValue.RealApprox a, ExactValue.ComplexApprox b -> SpecialFunctions.BesselI (a, b) |> fromComplex
        | ExactValue.ComplexApprox a, ExactValue.RealApprox b -> failwith "not supported"
        | ExactValue.ComplexApprox a, ExactValue.ComplexApprox b -> failwith "not supported"

    let besselk nu z =
        match nu, z with
        | ExactValue.RealApprox a, ExactValue.RealApprox b -> SpecialFunctions.BesselK (a, b) |> fromReal
        | ExactValue.RealApprox a, ExactValue.ComplexApprox b -> SpecialFunctions.BesselK (a, b) |> fromComplex
        | ExactValue.ComplexApprox a, ExactValue.RealApprox b -> failwith "not supported"
        | ExactValue.ComplexApprox a, ExactValue.ComplexApprox b -> failwith "not supported"

    let besseliratio nu z =
        match nu, z with
        | ExactValue.RealApprox a, ExactValue.RealApprox b -> SpecialFunctions.BesselIScaled (a + 1.0, b) / SpecialFunctions.BesselIScaled (a, b) |> fromReal
        | ExactValue.RealApprox a, ExactValue.ComplexApprox b -> SpecialFunctions.BesselIScaled (a + 1.0, b) / SpecialFunctions.BesselIScaled (a, b) |> fromComplex
        | ExactValue.ComplexApprox a, ExactValue.RealApprox b -> failwith "not supported"
        | ExactValue.ComplexApprox a, ExactValue.ComplexApprox b -> failwith "not supported"

    let besselkratio nu z =
        match nu, z with
        | ExactValue.RealApprox a, ExactValue.RealApprox b -> SpecialFunctions.BesselKScaled (a + 1.0, b) / SpecialFunctions.BesselKScaled (a, b) |> fromReal
        | ExactValue.RealApprox a, ExactValue.ComplexApprox b -> SpecialFunctions.BesselKScaled (a + 1.0, b) / SpecialFunctions.BesselKScaled (a, b) |> fromComplex
        | ExactValue.ComplexApprox a, ExactValue.RealApprox b -> failwith "not supported"
        | ExactValue.ComplexApprox a, ExactValue.ComplexApprox b -> failwith "not supported"

    let hankelh1 nu z =
        match nu, z with
        | ExactValue.RealApprox a, ExactValue.RealApprox b -> SpecialFunctions.HankelH1 (a, complex b 0.0) |> fromComplex
        | ExactValue.RealApprox a, ExactValue.ComplexApprox b -> SpecialFunctions.HankelH1 (a, b) |> fromComplex
        | ExactValue.ComplexApprox a, ExactValue.RealApprox b -> failwith "not supported"
        | ExactValue.ComplexApprox a, ExactValue.ComplexApprox b -> failwith "not supported"

    let hankelh2 nu z =
        match nu, z with
        | ExactValue.RealApprox a, ExactValue.RealApprox b -> SpecialFunctions.HankelH2 (a, complex b 0.0) |> fromComplex
        | ExactValue.RealApprox a, ExactValue.ComplexApprox b -> SpecialFunctions.HankelH2 (a, b) |> fromComplex
        | ExactValue.ComplexApprox a, ExactValue.RealApprox b -> failwith "not supported"
        | ExactValue.ComplexApprox a, ExactValue.ComplexApprox b -> failwith "not supported"

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
