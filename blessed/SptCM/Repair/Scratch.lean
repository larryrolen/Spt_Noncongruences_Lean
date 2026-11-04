module

public import blessed.SptCM.Repair.AnalyticFormalIdentification

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

#check tendsto_nhds_unique
#check tendsto_nhds_unique_of_eventuallyEq
#check Filter.Tendsto.congr'
#check Filter.tendsto_atTop.2
#check Filter.eventually_atTop.2
