`timescale 1ns/1ns // specify what "#1" means!

/* Observations in view of the project:
	Signals:
		Ready - rdy - it's only "1" when we find the gcd and "0" while processing it
	Start - start - it's "0" while processing the inputs, when the testbench send start = "1", it's to start to analyse the gcd
	Reset - rst - when it's "1", put every variable at 0
*/

module gcd_rtl #(parameter NBits = 2)
	(  
	input [NBits-1:0] xi, yi,
  	input rst, clk, start,

  	output reg [NBits-1:0] xo,
  	output reg rdy = 1'b0

	);

	reg signed [NBits-1:0] x, y;
	// Define the states
	parameter idle = 2'b00;
	parameter process_inputs = 2'b01;
	parameter calculate_gcd = 2'b10;

	reg [1:0] state, next_state;

	always @(posedge clk) begin
		if (rst) 
		begin
			// reset the state machine and all variables
			state <= idle;
			x <= 0;
			y <= 0;
			xo <= 0;
			rdy <= 0;
		end 
		else 
		begin
			// set the next state based on the current state
			case (state)
				idle: 
				begin
					if (start) 
					begin
						next_state <= process_inputs;
					end 
					else 
					begin	
						x <= xi;
						y <= yi;
						rdy <= 0;
						next_state <= idle;
					end
				end
				process_inputs: 
				begin
					if (x > 0 && y > 0) 
					begin
						next_state <= calculate_gcd;
					end 
					else if (x < 0 || y < 0) 
					begin
						if (x < 0) 
						begin
							x = -xi;
						end
						if (y < 0) 
						begin
							y = -yi;
						end
						//$display("%d %d", x, y);
						next_state <= process_inputs;
					end 
					else 
					begin
						xo <= 0;
						rdy <= 1'b1;
						next_state <= idle;
						//$display("rdy");
					end
				end
				calculate_gcd: 
				begin
					if (x != y) 
					begin
						if (y > x) 
						begin
							y <= y - x;
						end 
						else 
						begin
							x <= x - y; 
						end
						next_state <= calculate_gcd;
					end 
					else 
					begin
						xo <= x; // Can be xo <= y;
						rdy <= 1'b1;
						next_state <= idle;
						//$display("rdy");
					end
				end
				default: 
				begin
					next_state <= idle;
				end
			endcase
		end
	end

	// update the state
	always @(*) begin
		state <= next_state;
	end

endmodule

