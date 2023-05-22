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

class RandomNumber #(int NBits = 16);
    	rand bit [NBits-1:0] ar;
    	rand bit [NBits-1:0] br;

    	constraint a_fixed { ar[NBits-1] == 0; } //All the times be positive
	constraint b_fixed { br[NBits-1] == 0; }
endclass 

module gcd_tb;

  	// Parameters
  	parameter CLK_PERIOD = 10;
  	parameter CICLES = 10000;
	parameter NBits = 16;

  	// Inputs
  	reg [NBits-1:0] xi, yi;
  	reg rst, clk, start;

  	// Outputs
  	wire [NBits-1:0] xo;
  	wire [NBits-1:0] xo2;
  	wire rdy;
  	wire rdy2;


  	//Random Case
  	reg [NBits-1:0] a; //Only use 15 bits, because the 16 bit is to indicate its negative or positive, so in covergroup I need to ignore that
  	reg [NBits-1:0] b;
	RandomNumber #(NBits) randn;

  	reg [NBits-1:0] expected;
	integer i;
  	integer totalerrorsrandombeh = 0;
  	integer totalerrorsrandomrtl = 0;

	//Seeing how many inputs is cover in the random case -  Need to ignore the most significant bit because declre if it is positive or negative and in this case is all the times positive
	covergroup dinput @(posedge clk); //See if have every input number - random
  		pb1: coverpoint a[NBits-2:0];
		pb2: coverpoint b[NBits-2:0];
	endgroup

	covergroup cinput @(posedge clk); // See if have every input with every input - random
  		pb3: coverpoint a[NBits-2:0];
		pb4: coverpoint b[NBits-2:0];
		pb5: cross pb3,pb4;
	endgroup

	dinput dinput_inst;
	cinput cinput_inst;

	//Total of errors
  	integer totalerrorsbeh = 0;
  	integer totalerrorsrtl = 0;
	int fp2; //To save all the errors
	int line_number3 = 0;

	//From File
	int fp, fp1;
	int line_number;
	int line_number2 = 0;
	int val1;
	int val2;
	int count;

	//See if the output have every output possible between 0 to 1023
	covergroup doutput @(posedge clk); // See if have every output possible - All cases, only focus between 0 and 1023 because after that is almost impossible to have cases, needs to be prime the number and equal
  		pb6: coverpoint xo  
		{
            		bins MIN = {0};
            		bins MID[1023] = {[1:1022]};
            		bins MAX = {1023};
         	}
	endgroup

	doutput doutput_inst;
	
  	initial //Testing possible errors
	begin
		dinput_inst = new();
		doutput_inst = new();
		cinput_inst = new();

		fp2 = $fopen("errors.txt","w");
		if(fp2) $display("Opened the file to save the errors!");
		else 
		begin 
			$display("The files can't be opened!");
			$stop;
		end
    
   		// Test case 1: Calculate GCD of prime numbers
       		$display("Test case 1 : Calculate GCD of Prime Numbers");
		procedure(13,7);
      		//$display("  GCD(%d, %d) = %d", xi, yi, xo);
      		if (xo == 1) $display("	Prime Numbers - Test case passed - Behavioral");
      		else begin $display("	Prime Numbers - Test case failed: Expected 1, got %d - Behavioral", xo); totalerrorsbeh = totalerrorsbeh +1; $fdisplay(fp2, "Test Case 1 - Error: gcd(%d, %d) = %d, expected 1 - Behavioral", xi, yi, xo); line_number3 = line_number3 + 1; end
		if (xo2 == 1) $display("	Prime Numbers - Test case passed - RTL");
      		else begin $display("	Prime Numbers - Test case failed: Expected 1, got %d - RTL", xo2); totalerrorsrtl = totalerrorsrtl +1; $fdisplay(fp2, "Test Case 1 - Error: gcd(%d, %d) = %d, expected 1 - RTL", xi, yi, xo); line_number3 = line_number3 + 1; end
    
		
    		// Test case 2: Calculate GCD of  Equal Numbers - 65535 and 65535
    		$display("Test case 2 : Calculate GCD of Equal Numbers");
    		procedure(620,620);
      		//$display("  GCD(%d, %d) = %d", xi, yi, xo);
      		if (xo == 620) $display("	Equal Numbers - Test case passed - Behavioral");
      		else begin $display("	Equal Numbers - Test case failed: Expected %d, got %d - Behavioral", 620, xo); totalerrorsbeh = totalerrorsbeh +1; $fdisplay(fp2, "Test Case 2 - Error: gcd(%d, %d) = %d, expected %d - Behavioural", xi, yi, xo, 620); line_number3 = line_number3 + 1; end
      		if (xo2 == 620) $display("	Equal Numbers - Test case passed - RTL");
      		else begin $display("	Equal Numbers - Test case failed: Expected %d, got %d - RTL", 620, xo2); totalerrorsrtl = totalerrorsrtl +1; $fdisplay(fp2, "Test Case 2 - Error: gcd(%d, %d) = %d, expected %d - RTL", xi, yi, xo, 620); line_number3 = line_number3 + 1;end


		// Test case 3: Calculate GCD of 0 numbers
    		$display("Test case 3 : Calculate GCD of 0 Numbers");
		procedure(0,0);
      		//$display("  GCD(%d, %d) = %d", xi, yi, xo);
      		if (xo == 0) $display("	0 Numbers - Test case passed - Behavioral");
      		else begin $display("	0 Numbers - Test case failed: Expected 0, got %d - Behavioral", xo); totalerrorsbeh = totalerrorsbeh +1; $fdisplay(fp2, "Test Case 3 - Error: gcd(%d, %d) = %d, expected 0 - Behavioral", xi, yi, xo); line_number3 = line_number3 + 1; end
      		if (xo2 == 0) $display("	0 Numbers - Test case passed - RTL");
      		else begin $display("	0 Numbers - Test case failed: Expected 0, got %d - RTL", xo2); totalerrorsrtl = totalerrorsrtl +1; $fdisplay(fp2, "Test Case 3 - Error: gcd(%d, %d) = %d, expected 0 - RTL", xi, yi, xo); line_number3 = line_number3 + 1; end
      		
	
		// Test case 4: Calculate GCD of X > Y - 42 and 18
    		$display("Test case 4 : Calculate GCD of X > Y");
    		procedure(42,18);
      		//$display("  GCD(%d, %d) = %d", xi, yi, xo);
      		if (xo == 16'h6) $display("	X > Y - Test case passed - Behavioral");
      		else begin $display("	X > Y - Test case failed: Expected %d, got %d - Behavioral", 16'h6, xo); totalerrorsbeh = totalerrorsbeh +1; $fdisplay(fp2, "Test Case 4 - Error: gcd(%d, %d) = %d, expected %d - Behavioral", xi, yi, xo, 16'h6); line_number3 = line_number3 + 1; end
      		if (xo2 == 16'h6) $display("	X > Y - Test case passed - RTL");
      		else begin $display("	X > Y - Test case failed: Expected %d, got %d - RTL", 16'h6, xo2); totalerrorsrtl = totalerrorsrtl +1; $fdisplay(fp2, "Test Case 4 - Error: gcd(%d, %d) = %d, expected %d - RTL", xi, yi, xo, 16'h6); line_number3 = line_number3 + 1;  end
    

		// Test case 5: Calculate GCD of Y > X - 42 and 18
    		$display("Test case 5 : Calculate GCD of X > Y");
       		procedure(18,42);
      		//$display("  GCD(%d, %d) = %d", xi, yi, xo);
      		if (xo == 16'h6) $display("	Y > X - Test case passed - Behavioral");
      		else begin $display("	Y > X - Test case failed: Expected %d, got %d - Behavioral", 16'h6, xo); totalerrorsbeh = totalerrorsbeh +1; $fdisplay(fp2, "Test Case 5 - Error: gcd(%d, %d) = %d, expected %d - Behavioral", xi, yi, xo, 16'h6); line_number3 = line_number3 + 1; end
      		if (xo2 == 16'h6) $display("	Y > X - Test case passed - RTL");
      		else begin $display("	Y > X - Test case failed: Expected %d, got %d - RTL", 16'h6, xo2); totalerrorsrtl = totalerrorsrtl +1; $fdisplay(fp2, "Test Case 5 - Error: gcd(%d, %d) = %d, expected %d - RTL", xi, yi, xo, 16'h6); line_number3 = line_number3 + 1;  end
		
		// Test case 6: Calculate GCD of Negative Numbers - I use the abs
    		$display("Test case 6 : Calculate GCD of Negative Numbers - Using the abs");
       		procedure(-18,-42);
      		//$display("  GCD(%d, %d) = %d", xi, yi, xo);
      		if (xo == 16'h6) $display("	Negative Numbers - Test case passed - Behavioral");
      		else begin $display("	Negative Numbers - Test case failed: Expected %d, got %d - Behavioral", 16'h6, xo); totalerrorsbeh = totalerrorsbeh +1; end
      		if (xo2 == 16'h6) $display("	Negative Numbers - Test case passed - RTL");
      		else begin $display("	Negative Numbers - Test case failed: Expected %d, got %d - RTL", 16'h6, xo2); totalerrorsrtl = totalerrorsrtl +1; end
		procedure(-18,42);
		if (xo == 16'h6) $display("	Negative Numbers - Test case passed - Behavioral");
      		else begin $display("	Negative Numbers - Test case failed: Expected %d, got %d - Behavioral", 16'h6, xo); totalerrorsbeh = totalerrorsbeh +1; end
      		if (xo2 == 16'h6) $display("	Negative Numbers - Test case passed - RTL");
      		else begin $display("	Negative Numbers - Test case failed: Expected %d, got %d - RTL", 16'h6, xo2); totalerrorsrtl = totalerrorsrtl +1; end
		procedure(18,-42);
		if (xo == 16'h6) $display("	Negative Numbers - Test case passed - Behavioral");
      		else begin $display("	Negative Numbers - Test case failed: Expected %d, got %d - Behavioral", 16'h6, xo); totalerrorsbeh = totalerrorsbeh +1; end
      		if (xo2 == 16'h6) $display("	Negative Numbers - Test case passed - RTL");
      		else begin $display("	Negative Numbers - Test case failed: Expected %d, got %d - RTL", 16'h6, xo2); totalerrorsrtl = totalerrorsrtl +1; end
    		


    		// Test case 7: Calculate GCD of Random Numbers
		$display("Test case 7: Calculate GCD of %d Random Numbers", CICLES);
		randn = new();
		repeat (CICLES) 
    		begin
      			// Generate random input values
			
			randn.randomize();
      			//a = $random;
      			//b = $random;
			a = randn.ar;
			b = randn.br;
			expected = 0;
      		
			procedure(a, b);

      			// Calculate the expected result
      			
      			for (i = 1; i <= a && i <= b; i++) 
			begin
        			if (a % i == 0 && b % i == 0) expected = i; //	Increase i between 2 and the max number between a and b and see when the rest of the both numbers are 0
        		end

      			// Check the result of Behavioural
      			if (xo != expected) 
			begin
        			$display("	Error: gcd(%d, %d) = %d, expected %d", xi, yi, xo, expected);
        			totalerrorsbeh = totalerrorsbeh + 1;
				totalerrorsrandombeh = totalerrorsrandombeh + 1;
				$fdisplay(fp2, "Test Case 7 - Error: gcd(%d, %d) = %d, expected %d - Behavioral", xi, yi, xo, expected); line_number3 = line_number3 + 1; 
      			end

      			// Check the result of RTL
      			if (xo2 != expected) 
			begin
        			$display("	Error: gcd(%d, %d) = %d, expected %d", xi, yi, xo2, expected);
        			totalerrorsrtl = totalerrorsrtl + 1;
				totalerrorsrandomrtl = totalerrorsrandomrtl + 1;
				$fdisplay(fp2, "Test Case 7 - Error: gcd(%d, %d) = %d, expected %d - RTL", xi, yi, xo, expected); line_number3 = line_number3 + 1; 
      			end
		
    		end
		
		if (totalerrorsrandombeh != 0) $display("	Number of Errors Random: %d - Behavioral", totalerrorsrandombeh);
    		else $display("	All tests of Numbers Random passed! - Behavioral");

    		if (totalerrorsrandomrtl != 0) $display("	Number of Errors Random: %d - RTL", totalerrorsrandomrtl);
    		else $display("	All tests of Numbers Random passed! - RTL");
		
		
		// Test case 8: Calculate GCD of Numbers Gotten from a file
		$display("Test case 8: Calculate GCD of Numbers Gotten from a file");
		wait(clk);

		fp = $fopen("datafromafile.txt","r");
		fp1 = $fopen("resultsfromafile.txt","w");

		if(fp & fp1) $display("	Opened the files!");
		else 
		begin 
			$display("	The files can't be opened!");
			$stop;
		end
			

		while(!$feof(fp)) 
		begin 
			count = $fscanf(fp, "%d %d %d", line_number,val1,val2);
			if(count == 3) 
			begin //$display("%t\t%d %d %d", $time, line_number, val1, val2); //Number of input data
					
				expected = 0;
      					
				procedure(val1, val2);

     				// Calculate the expected result
      			
      				for (i = 1; i <= val1 && i <= val2; i++) 
				begin
        				if (val1 % i == 0 && val2 % i == 0) expected = i; //	Increase i between 2 and the max number between a and b and see when the rest of the both numbers are 0
        			end

      				// Check the result of Behavioural
      				if (xo != expected) 
				begin
        				$display("	Error: gcd(%d, %d) = %d, expected %d", xi, yi, xo, expected); totalerrorsbeh = totalerrorsbeh + 1;
					$fdisplay(fp1, "Line %d: Error: gcd(%d, %d) = %d, expected %d - Behavioral", line_number2, xi, yi, xo, expected); line_number2 = line_number2 + 1;
					$fdisplay(fp2, "Test Case 8 - Error: gcd(%d, %d) = %d, expected %d - Behavioral", xi, yi, xo, expected); line_number3 = line_number3 + 1; 
      				end

      				// Check the result of RTL
      				if (xo2 != expected) 
				begin
        				$display("	Error: gcd(%d, %d) = %d, expected %d", xi, yi, xo2, expected); totalerrorsrtl = totalerrorsrtl + 1;
	  				$fdisplay(fp1, "Line %d: Error: gcd(%d, %d) = %d, expected %d - RTL", line_number2, xi, yi, xo, expected); line_number2 = line_number2 + 1;
					$fdisplay(fp2, "Test Case 8 - Error: gcd(%d, %d) = %d, expected %d - RTL", xi, yi, xo, expected); line_number3 = line_number3 + 1; 
      				end
					
				#20;
			end

		end
		
		$fclose(fp);
		$fclose(fp1);
		
		

    		if (totalerrorsbeh != 0) begin $display("Number of Errors in total: %d - Behavioral", totalerrorsbeh); $fdisplay(fp2, "Number of Errors in total: %d - Behavioral", totalerrorsbeh); line_number3 = line_number3 + 1; end
    		else begin $display("All tests passed! - Behavioral"); $fdisplay(fp2, "All tests passed! - Behavioral"); line_number3 = line_number3 + 1; end

    		if (totalerrorsrtl != 0) begin $display("Number of Errors in total: %d - RTL", totalerrorsrtl); $fdisplay(fp2, "Number of Errors in total: %d - RTL", totalerrorsrtl); line_number3 = line_number3 + 1; end
    		else begin $display("All tests passed! - RTL"); $fdisplay(fp2, "All tests passed! - RTL"); line_number3 = line_number3 + 1; end
    
		$fclose(fp2);
		
    		$stop; // Stop the simulation
 	end

	//Controlling the Clk signal
	initial
	begin
		clk = 1'b0;
		forever
    			# (CLK_PERIOD / 2 ) clk = ~clk;
	end

	//Task that execute the reset signal and update the numbers
	task procedure;
	input [NBits-1:0] x,y;
	begin
		rst = 1'b1;
		//$display("Time after rst = 1'b1: %t", $time);
		#1;
		rst = 1'b0;
		//$display("Time after rst = 1'b0: %t", $time);
		xi = x;
    		yi = y; 
		start = 1'b0;

    		// Wait for a few clock cycles
    		# (CLK_PERIOD * 5) start = 1'b1;

		@(posedge rdy, posedge rdy2); // Both are at same time, I use the ",", because in this version works like a and (&)
		
		if(!rdy || !rdy2) @(posedge rdy, posedge rdy2); 

		start = 1'b0;
	end
	endtask

  	// Instantiate the Unit Under Test (UUT) this case Behavioural
  	gcd_behavioural #(.NBits(NBits)) beh(
    		.xi(xi),
    		.yi(yi),
    		.rst(rst),
    		.xo(xo),
    		.rdy(rdy),
    		.clk(clk),
		.start(start)
  	);

  	// Instantiate the Unit Under Test (UUT) this case RTL
  	gcd_rtl #(.NBits(NBits)) rtl (
    		.xi(xi),
    		.yi(yi),
    		.rst(rst),
    		.xo(xo2),
    		.rdy(rdy2),
    		.clk(clk),
		.start(start)
  	);

	bind gcd_behavioural: beh pLib_gcd_rtl  #(.NBits(NBits)) pLgr (
		.xi(xi), 
		.yi(yi), 
		.rst(rst), 
		.xo(xo), 
		.rdy(rdy), 
		.clk(clk), 
		.start(start)
	);

endmodule
