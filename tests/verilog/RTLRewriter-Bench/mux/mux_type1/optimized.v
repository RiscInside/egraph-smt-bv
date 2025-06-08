module optimized(
    input wire sel,
    input wire a,
    input wire b,
    input wire c,
    output wire y
);
    wire x0;
    optimized_simple_cal cal0(.in(a), .out(x0));
    optimized_mux2to1 mux1 (.in0(x0), .in1(c), .sel(sel), .out(y));
endmodule

// 2-to-1 Multiplexer Module
module optimized_mux2to1(
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
module optimized_simple_cal(
    input wire in,
    output reg out
);
    always @(*) begin
          out = in << 2 + 1;
    end
endmodule
