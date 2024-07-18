import gen_fifo_defines_pkg::*;

module fv_funct_generator_register_i(
	input  logic 		       		clk,
	input  logic 		        	rst,
	input  logic 		        	clrh,
	input  logic 		        	enh,
	input  logic [`DATA_WIDTH - 1:0]	d,
	input  logic [`DATA_WIDTH - 1:0] 	q	
);
  	bit flag;
 
  	always @(posedge clk) begin
      	if (rst == 1'b1)
        	flag <= 1'b0;
      	else 
        	flag <=1'b1;
  	end

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1)

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures  that when rst is active, q should be RESET_VALUE. //adding RESET_AMP for the amp_reg instance
 	 when_rst_1_q_is_reset_value: assert property (@(posedge clk) (!flag) |-> (q == `RESET_VALUE || `RESET_AMP)) $info("Assetion pass when_rst_1_q_is_reset_value");
	else $error(" Asserion fail when_rst_1_q_is_reset_value");
	
	// 2) The property assures  that when clrh is active, q should be RESET_VALUE.
    	when_clrh_1_q_is_reset_value: assert property (@(posedge clk) clrh |=> (q == `RESET_VALUE)) $info("Assetion pass when_clrh_1_q_is_reset_value");
	else $error(" Asserion fail when_clrh_1_q_is_reset_value");

	// 3) The property assures that when enh is active, q should be equal to d.
	when_ehn_1_q_is_d: assert property (@(posedge clk) (enh) |=> (q == $past(d))) $info("Assetion pass when_ehn_1_q_is_d");
	else $error(" Asserion fail when_ehn_1_q_is_d");

	// 4) The property assures that when neither enh, clrh, nor rst is active, q should hold its previous value.
        q_holds_prev_value: assert property (@(posedge clk)  ((!enh) && (!clrh) && (flag)) |=> (q == $past(q))) $info("Assetion pass q_holds_prev_value");
	else $error(" Asserion fail q_holds_prev_value");

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
	
	// 1) Covers when rst happen.
	cover_rst: cover property (@(posedge clk) $rose(flag));

	// 2) Covers when clrh happen. //clhr is always 0 at top level
	cover_clrh: cover property (@(posedge clk)(clrh));

	// 3) Covers when enh happen.
	cover_enh: cover property (@(posedge clk) (enh));

endmodule

bind funct_generator_register fv_funct_generator_register_i fv_generator_register_i_inst(.*);
