import * as lean from "./hacky-lean-runtime.js";

export const instructions = lean.graph;

x = (bvar_0) =>
  ((bvar_1) =>
    ((bvar_2) =>
      ((bvar_3) =>
        leanprim.stack(
          leanprim.cons(
            leanprim.line(leanprim.tuple(lean.x, 0), leanprim.tuple(0, 100)),
            leanprim.cons(
              leanprim.line(leanprim.tuple(0, 0), leanprim.tuple(100, 0)),
              leanprim.cons(
                leanprim.func((bvar_4) => bvar_3 + bvar_2 * bvar_4),
                leanprim.cons(
                  leanprim.circle(leanprim.tuple(bvar_0, bvar_1(bvar_0)), 20),
                  leanprim.cons(leanprim.func(bvar_1), leanprim.nil())
                )
              )
            )
          )
        ))(bvar_1(bvar_0) - bvar_0 * bvar_2))(
      (bvar_1(bvar_0 + 1e-3) - bvar_1(bvar_0 - 1e-3)) / 2e-3
    ))((bvar_1) => -3e-2 * bvar_1 * bvar_1 + 27e-1 * bvar_1 + 10);
