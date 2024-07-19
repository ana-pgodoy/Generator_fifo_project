import gen_fifo_defines_pkg::*;

module fv_funct_generator_lut_i #(
	parameter DATA_WIDTH = 	`DATA_WIDTH,
	parameter ADDR_WIDTH = 	`LUT_ADDR	 
)( 
	input  logic                  		clk,		
	input  logic [ADDR_WIDTH-1:0] 		read_addr_i,
	input logic signed [DATA_WIDTH-1 : 0] 	read_data_o,
	reg [DATA_WIDTH-1 : 0] lut_structure [2**ADDR_WIDTH-1:0]
);
	`define RST_PATH fv_generator_inst.rst
	bit flag;

  	always @(posedge clk) begin
      	if (`RST_PATH == 1'b1)
        	flag <= 1'b0;
      	else 
        	flag <=1'b1;
  	end

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assumes that the address provided for reading is always within the valid range.
	assume property (@(posedge clk) read_addr_i < (2**ADDR_WIDTH));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures  that the read_data_o signal does not contain any unknown values.
	read_data_o_valid: assert property (@(posedge clk) read_addr_i |=> $isunknown(read_data_o) == 0) $info("Assetion pass read_data__o_valid");
	else $error(" Asserion fail read_data__o_valid");
	
	// 2) The property assures that the read address (read_addr_i) is within the valid range of addresses for the LUT
	read_addr_i_valid_range: assert property (@(posedge clk) read_addr_i < (2**ADDR_WIDTH)) $info("Assetion pass read_addr_i_valid_range");
	else $error(" Asserion fail read_addr_i_valid_range");	
	
	// 3) The property assures that if read_addr_i request then the read_data_o should match the value stored in lut_structure at read_addr_i //changin read_addr_i for a flag to evaluate all the time after reset and |=> for |->
	read_data_o_when_valid_read_addr_i: assert property (@(posedge clk) flag |-> (read_data_o == lut_structure[$past(read_addr_i)])) $info("Assetion pass read_data_o_when_valid_read_addr_i");
	else $error(" Asserion fail read_data_o_when_valid_read_addr_i");
 

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
	
	// 1) Covers that read operation occurs at least once.
	 cover_read_operation: cover property (@(posedge clk) read_addr_i && (read_data_o == lut_structure[$past(read_addr_i)]));
  	
	// 2) Covers that output data does not contain unknown values.
	cover_read_data_o_valid: cover property (@(posedge clk) $isunknown(read_data_o) == 0);
  	
	// 3) Covers valid address increment.
	cover_read_add_i_incrementing: cover property (@(posedge clk) (read_addr_i == $past(read_addr_i) + 1));

	//4) Cover properties to ensure all LUT addresses are accessed
	cover_all_addresses: cover property (@(posedge clk) read_addr_i == (2**ADDR_WIDTH-1));

endmodule

bind funct_generator_lut fv_funct_generator_lut_i fv_generator_lut_i_inst(.*);
