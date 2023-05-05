module pLib_gcd_rtl #(parameter NBits = 16) //didnt change
	(
	// Inputs
	input [NBits-1:0] xi, yi, xo,
  	input rst, clk, start, rdy
	);

	
	
	equal_numbers: assert property (
			@(posedge clk) ($rose(rdy) && xi == yi && xi != 0) |-> (xo == xi));

	zero_number: assert property (
			@(posedge clk) ($rose(rdy) && (xi == 0 || yi == 0)) |-> (xo == xi + yi));


	//Cover 
	property outputxo(value); //Cover Output between 0 and 25 
  		xo == value;
	endproperty;

	property inputxi(value); //Cover Input Xi between 0 and 25
  		xi == value;
	endproperty;

	property inputyi(value); //Cover Input Yi between 0 and 25
  		yi == value;
	endproperty;



	genvar i;
	generate
  		for (i = 0; i <= 25; i++) begin : 
		output_ cover property (@(posedge clk) outputxo(i));
  		end
	endgenerate

	

	genvar a;
	generate
  		for (a = 0; a <= 25; a++) begin : 
		input_xi_ cover property (@(posedge clk) inputxi(a));
  		end
	endgenerate

	
	genvar b;
	generate
  		for (b = 0; b <= 25; b++) begin : 
		input_yi_ cover property (@(posedge clk) inputyi(b));
  		end
	endgenerate


endmodule
