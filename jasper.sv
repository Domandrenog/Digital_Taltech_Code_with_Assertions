`timescale 1ns/1ns
// specify what "#1" means!

/* 
Types of tests:
	Prime Numbers - the result is gonna be = 1
	Equal Numbers - the result is gonna be the number
	One be 0 - the result will be 0
	X be greater than Y
	Y be greater than X
	Negative Numbers 
	Random Numbers
	Read from a file
*/


module gcd_tb(

  	// Inputs
  	input reg [15:0] xi, yi,
  	input reg rst, clk, start,
  	output [15:0] xo,
  	output rdy
	);

  	// Parameters
	parameter NBits = 16;


  	// Instantiate the Unit Under Test (UUT) this case RTL
  	gcd_rtl #(.NBits(NBits)) rtl (
    		.xi(xi),
    		.yi(yi),
    		.rst(rst),
    		.xo(xo),
    		.rdy(rdy),
    		.clk(clk),
		.start(start)
  	);

	bind gcd_rtl: rtl pLib_gcd_rtl  #(.NBits(NBits)) pLgr (
		.xi(xi), 
		.yi(yi), 
		.rst(rst), 
		.xo(xo), 
		.rdy(rdy), 
		.clk(clk), 
		.start(start)
	);

endmodule
