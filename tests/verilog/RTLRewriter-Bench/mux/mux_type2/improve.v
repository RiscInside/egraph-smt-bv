module improve(
    input wire a,
    input wire b,
    output wire y
);
    wire x;
    improve_simple_cal cal0(.in(1), .out(x));
    improve_mux2to1 mux0 (.in0(a), .in1(x), .sel(b), .out(y));
endmodule

// 2-to-1 Multiplexer Module
module improve_mux2to1(
    input wire in0,
    input wire in1,
    input wire sel,
    output reg out
);
    always @(*) begin
        out = sel ? in1 : in0; // Use ternary operator for clarity
    end
endmodule

// simple calculation
module improve_simple_cal(
    input wire in,
    output reg out
);
    always @(*) begin
          out = (in << 2) + 1;
    end
endmodule
