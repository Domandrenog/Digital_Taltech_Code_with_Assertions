module pLib_gcd_rtl #(parameter NBits = 2) //didnt change
	(
	// Inputs
	input [NBits-1:0] xi, yi, xo,
  	input rst, clk, start, rdy
	);

	
	
	//equal_numbers: assert property (
			//@(posedge clk) ($rose(rdy) && xi == yi && xi != 0) |-> (xo == xi));
	/*
	equal_numbers: assert property (
    			@(posedge clk) ($fell(start) && xi == yi && xi != 0) |-> ##1 (xo == xi))
    			else $error($sformatf("Test case failed: expected xo=%0d, but got xo=%0d", xi, xo));

	
	zero_number: assert property (
			@(posedge clk) ($rose(rdy) && (xi == 0 || yi == 0)) |-> (xo == xi + yi))
			else $error($sformatf("Test case failed: expected xo=%0d, but got xo=%0d", xi, xo));
	*/


	//NBits should be a positive integer
	NBits_integer: assert property (
			@(posedge clk) ($rose(rdy)) |-> (NBits > 0)) else $error("NBits must be a positive integer");
	
	//xi and yi should be valid 2^NBits-bit numbers:
	Xi_betweenlimits: assert property(
			@(posedge clk) ($rose(rdy)) |-> ($signed(xi) >= -(1 << (NBits-1)) && $signed(xi) < (1 << (NBits-1)))) else $error("xi is not a valid %0d-bit signed number", NBits);
	Yi_betweenlimits: assert property(
			@(posedge clk) ($rose(rdy)) |-> ($signed(yi) >= -(1 << (NBits-1)) && $signed(yi) < (1 << (NBits-1)))) else $error("yi is not a valid %0d-bit signed number", NBits);

	// rst, clk, and start should be either 0 or 1:
	Rst_betweenlimits: assert property( 
			@(posedge clk) ($rose(rdy)) |-> (rst === 0 || rst === 1)) else $error("rst must be 0 or 1");
	Clk_betweenlimits: assert property( 
			@(posedge clk) ($rose(rdy)) |-> (clk === 0 || clk === 1)) else $error("clk must be 0 or 1");
	Start_betweenlimits: assert property( 
			@(posedge clk) ($rose(rdy)) |-> (start === 0 || start === 1)) else $error("start must be 0 or 1");
	Rdy_betweenlimits: assert property( 
			@(posedge clk) ($rose(rdy)) |-> (rdy === 0 || rdy === 1)) else $error("rdy must be 0 or 1");





	

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
