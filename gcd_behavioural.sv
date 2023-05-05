`timescale 1ns/1ns // specify what "#1" means!

/* Observations in view of the project:
	Signals:
		Ready - rdy - it's only "1" when we find the gcd and "0" while processing it
		Start - start - it's "0" while processing the inputs, when the testbench send start = "1", it's to start to analyse the gcd
		Reset - rst - when it's "1", put every variable at 0
*/

module gcd_behavioural #(parameter NBits = 2)
	(  
	input [NBits-1:0] xi, yi,
  	input rst, clk, start,

  	output reg [NBits-1:0] xo,
  	output reg rdy = 1'b0

	);


  reg signed [NBits-1:0] x, y;


  always @(posedge clk)
  begin
	if (start == 1'b0 && rst == 1'b0)   // Can be a while with a delay
	begin
        	x <= xi;
        	y <= yi;
		rdy <= 0;
      	end 

    	else if (start == 1'b1 && rst == 1'b0)
	begin	
		if( x > 0 && y > 0) 
		begin		
        		while (x != y) // will perform all in the same clk cycle - so its needed to add a delay
			begin
				//for while i need to use blocking, only if I not use a delay!!
          			if (y > x)  		y = y - x;  
				else 		 	x = x - y; 
				
				@(posedge clk); //#10; - It's the same

			end
        		xo <= x; //Can be xo <= y;
        		rdy <= 1'b1;
		end
		else if (x < 0 || y < 0)
		begin
			if(x<0)	x = -xi;
			if (y<0)   y = -yi; 
			//$display("%d and %d", x, y);
		end
		else 
		begin	
			xo <= 0; 
        		rdy <= 1'b1;
		end
	end
	else
	begin
		x <= 0;
        	y <= 0;
		rdy <= 0;
	end

    end

endmodule
