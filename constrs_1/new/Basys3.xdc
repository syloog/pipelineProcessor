set_property PACKAGE_PIN W5 [get_ports clk]       
 set_property IOSTANDARD LVCMOS33 [get_ports clk]
 create_clock -add -name sys_clk_pin -period 10.00 -waveform {0 5} [get_ports clk]

set_property PACKAGE_PIN V17 [get_ports reset]						
      set_property IOSTANDARD LVCMOS33 [get_ports reset]
set_property PACKAGE_PIN V16 [get_ports clear]						
      set_property IOSTANDARD LVCMOS33 [get_ports clear]
set_property PACKAGE_PIN U18 [get_ports switch]						
      set_property IOSTANDARD LVCMOS33 [get_ports switch]

set_property PACKAGE_PIN V19 [get_ports stallF]						
      set_property IOSTANDARD LVCMOS33 [get_ports stallF]
set_property PACKAGE_PIN U19 [get_ports stallD]						
      set_property IOSTANDARD LVCMOS33 [get_ports stallD]
set_property PACKAGE_PIN E19 [get_ports FlushE]						
      set_property IOSTANDARD LVCMOS33 [get_ports FlushE]
set_property PACKAGE_PIN U16 [get_ports FlushM]						
      set_property IOSTANDARD LVCMOS33 [get_ports FlushM]


set_property PACKAGE_PIN W7 [get_ports {a}]
      set_property IOSTANDARD LVCMOS33 [get_ports {a}]
set_property PACKAGE_PIN W6 [get_ports {b}]                    
      set_property IOSTANDARD LVCMOS33 [get_ports {b}]
set_property PACKAGE_PIN U8 [get_ports {c}]                    
      set_property IOSTANDARD LVCMOS33 [get_ports {c}]
set_property PACKAGE_PIN V8 [get_ports {d}]                    
      set_property IOSTANDARD LVCMOS33 [get_ports {d}]
set_property PACKAGE_PIN U5 [get_ports {e}]                    
      set_property IOSTANDARD LVCMOS33 [get_ports {e}]
set_property PACKAGE_PIN V5 [get_ports {f}]                    
      set_property IOSTANDARD LVCMOS33 [get_ports {f}]
set_property PACKAGE_PIN U7 [get_ports {g}]                    
      set_property IOSTANDARD LVCMOS33 [get_ports {g}]
         
set_property PACKAGE_PIN V7 [get_ports dp]
      set_property IOSTANDARD LVCMOS33 [get_ports dp]


set_property PACKAGE_PIN U2 [get_ports {an[0]}]                    
      set_property IOSTANDARD LVCMOS33 [get_ports {an[0]}]
set_property PACKAGE_PIN U4 [get_ports {an[1]}]                    
      set_property IOSTANDARD LVCMOS33 [get_ports {an[1]}]
set_property PACKAGE_PIN V4 [get_ports {an[2]}]                    
      set_property IOSTANDARD LVCMOS33 [get_ports {an[2]}]
set_property PACKAGE_PIN W4 [get_ports {an[3]}]                    
      set_property IOSTANDARD LVCMOS33 [get_ports {an[3]}]