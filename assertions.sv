`timescale 1ns/1ns

module pLib_gcd_rtl #(parameter NBits = 2) //didnt change
	(
	// Inputs
	input [NBits-1:0] xi, yi, xo,
  	input rst, clk, start, rdy
	);



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


	/*
	// Sequence assertion for rst = 1'b1 followed by rst = 1'b0
	sequence rst_assertion_seq(t_value);
 	 (rst == t_value) ##1 (rst == t_value);
	endsequence;

	rst_property: assert property(
  	@(posedge clk) rst_assertion_seq(1) |=> rst_assertion_seq(0));
	*/


	/* Test times it will be wrong
	// Sequence assertion for rst = 1'b1 followed by rst = 1'b0
	sequence rst_assertion_seq;
 		@(posedge rst) rst == 1'b1 ##[1:$] @(negedge rst) rst == 1'b0;
	endsequence;

	// Property for rst_assertion_seq
	property rst_property;
	  @(posedge rst) rst_assertion_seq;
	endproperty;

	// Assertion of rst_property
	assert property (rst_property) else $display("Assertion error: rst = 1'b1 followed by rst = 1'b0 not satisfied at time %t", $time);
	*/


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
