export const Bool_true = true;
export const Bool_false = false;

export const HMul_hMul = (_) => (_) => (_) => (_) => (x) => (y) => x * y;
export const instMulFloat = "instAddFloat";
export const instHMul = (_) => (_) => "instHMul";

export const Neg_neg = (_) => (_) => (x) => -x;
export const instNegFloat = "instNegFloat";

export const HAdd_hAdd = (_) => (_) => (_) => (_) => (x) => (y) => x + y;
export const instAddFloat = "instAddFloat";
export const instHAdd = (_) => (_) => "instHAdd";

export const HSub_hSub = (_) => (_) => (_) => (_) => (x) => (y) => x - y;
export const instSubFloat = "instSubFloat";
export const instHSub = (_) => (_) => "instHSub";

export const HDiv_hDiv = (_) => (_) => (_) => (_) => (x) => (y) => x / y;
export const instDivFloat = "instDivFloat";
export const instHDiv = (_) => (_) => "instHDiv";

export const Float = "number";
export const OfNat_ofNat = (_) => (_) => (n) => n;
export const instOfNatFloat = (n) => Number(n);

export const OfScientific_ofScientific =
  (_) => (_) => (base) => (neg) => (exp) =>
    Number(base) * Math.pow(10, Number(neg ? -exp : exp));
export const instOfScientificFloat = "";

export const Splat = "splat";

export const Splat_stack = (x) => x;
export const Splat_line = (start) => (end) => ({
  type: "line",
  start,
  end,
});
export const Splat_circle = (center) => (diameter) => ({
  type: "circle",
  center,
  diameter,
});
export const Splat_func = (func) => ({ type: "func", func });

export const List_cons = (_) => (hd) => (tl) => [hd, tl];
export const List_nil = (_) => null;

export const Prod_mk = (_) => (_) => (x) => (y) => [x, y];

export const List_toArray = (t) => (list) => {
  const ret = [];
  while (list !== null) {
    ret.push(list[0]);
    list = list[1];
  }
  return ret;
};
