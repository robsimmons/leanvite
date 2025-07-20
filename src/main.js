import { p5 } from "p5js-wrapper";
import { instructions } from "./generated-data-from-lean";

const slider = document.querySelector("#slider");
slider.onchange = () => console.log(slider.value);

function x(p) {
  return 3 * p + 10;
}

function y(p) {
  return 310 - 3 * p;
}

new p5((p) => {
  p.setup = () => {
    p.createCanvas(320, 320);
  };

  function drawSplat(instr) {
    if (Array.isArray(instr)) {
      for (const subInstr of instr) {
        drawSplat(subInstr);
      }
    }
    switch (instr.type) {
      case "line": {
        p.line(
          x(instr.start[0]),
          y(instr.start[1]),
          x(instr.end[0]),
          y(instr.end[1])
        );
        break;
      }
      case "func": {
        let lx = x(0);
        let ly = y(instr.func(0));
        for (let i = 0; i < 100; i++) {
          const nx = x(i + 1);
          const ny = y(instr.func(i + 1));
          p.line(lx, ly, nx, ny);
          lx = nx;
          ly = ny;
        }
        break;
      }
      case "circle": {
        p.circle(x(instr.center[0]), y(instr.center[1]), instr.diameter);
      }
      default: {
        console.warn(`Unexpected splat instruction ${instr.type}`);
      }
    }
  }

  p.draw = () => {
    p.background(220);
    try {
      drawSplat(instructions(Number(slider.value)));
    } catch (e) {
      console.error(`Error evaluating splat: ${e}`);
    }
  };
}, "display");
