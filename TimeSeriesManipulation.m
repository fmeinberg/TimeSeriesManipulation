BeginPackage["TimeSeriesManipulation`", {"DateTools`"}]

(* This package operates on lists of the form {{date, value} ...}, where date is a date in list format and value is any Mathematica expression. This is the canonical time series format returned by Mathematica functions such as CountryData and FinancialData. *)

Earliest::usage="";
Latest::usage="";
TimeSeriesTake::usage="";
TimeSeriesIntersection::usage="";
TimeSeriesUnion::usage="";
TimeSeriesMerge::usage="";
TimeSeriesApply::usage="";
TimeSeriesMap::usage="";
TimeSeriesDateMap::usage="";
TimeSeriesThread::usage="";
TimeSeriesMapThread::usage="";
TimeSeriesListConvolve::usage="";
TimeSeriesListCorrelate::usage="";
TimeSeriesGatherByDate::usage="";
TimeSeriesGatherBy::usage="";
TimeSeriesMovingMap::usage="";
TimeSeriesMovingAverage::usage="";
TimeSeriesMovingMedian::usage="";
TimeSeriesDifferences::usage="";
TimeSeriesRatios::usage="";
TimeSeriesLag::usage="";
TimeSeriesFold::usage="";
TimeSeriesAccumulate::usage="";
TimeSeriesNormalize::usage="";
TimeSeriesInterpolation::usage="";
TimeSeriesLinearFilter::usage="";
TimeSeriesSeasonFilter::usage="";
TimeSeriesSelect::usage="";
TimeSeriesBinLists::usage="";
TimeSeriesMean::usage="";
TimeSeriesBinMeans::usage="";
TimeSeriesBinTotals::usage="";
TimeSeriesDateMin::usage="";
TimeSeriesDateMax::usage="";

Begin["Private`"]

(* Auxiliary function to deal with Missing values *)

MissingAlgebra[foo_]:= If[FreeQ[{##},Missing], foo[##],Missing["NotAvailable"]]&

(* Take, Earliest, Latest *)

Earliest[series_, n_:1]:=
	SortBy[series, AbsoluteTime@First@#&][[;;n]]

Latest[series_, n_:1]:=
	SortBy[series, AbsoluteTime@First@#&][[-n;;]]

TimeSeriesTake[series_, dates:{startDate_, endDate_}]:=
	Block[{sd, ed},
		sd = startDate /. {All -> - Infinity, _ :> AbsoluteTime@startDate};
		ed = endDate /. {All -> Infinity, _ :> AbsoluteTime@endDate};
		Select[series, OrderedQ[{sd, AbsoluteTime@#[[1]], ed}]&]
	]

(* Aligning time series *)

TimeSeriesIntersection[series_] :=
    Block[ {commonQ, commonDates = Intersection@@series[[All,All,1]],commonData},
        commonQ[_] = False;
        (commonQ@# = True)&/@commonDates;
        Pick[#, commonQ/@#[[All,1]]]&/@series
    ]

TimeSeriesUnion[series_] :=
 Block[{alldates, f}, alldates = Union @@ series[[All, All, 1]];
  f[_][_] = Missing["NotAvailable"];
  MapIndexed[
   Function[{s, i}, (Set[f[First@i][#1], #2]) & @@@
      s], series];
  Table[{#, f[i][#]} & /@ alldates, {i, Length@series}]]

TimeSeriesMerge[series_]:=
	SortBy[Apply[Join, series], First]

(* Apply *)

TimeSeriesApply[f_, series_, rest___]:=
	Apply[f, series[[All,2]], rest]

(* Map *)

TimeSeriesMap[f_, series_] :=
   With[{missF=MissingAlgebra@f}, {#1, missF@#2}&@@@series]

TimeSeriesDateMap[f_, series_]:=
	  {f@#1, #2}&@@@series

(* Thread *)

TimeSeriesThread[series_] :=
 Transpose[Function[item, {First@item, #} & /@ Rest@item] /@ series]

(* MapThread *)

TimeSeriesMapThread[f_, series_] :=
    Block[ {missF=MissingAlgebra@f, aligned = TimeSeriesIntersection@series, dates, data},
        dates = aligned[[All,All,1]][[1]];
        Transpose@{dates, MapThread[missF, aligned[[All,All,2]]]}
    ];

(* ListConvolve and ListCorrelate *)

TimeSeriesListConvolve[ker_, list_, klist_, padding_, f_, g_, lev_:1] :=
    Block[ {d,missF=MissingAlgebra@f, missG=MissingAlgebra@g},
        ListConvolve[ker, d@@@list, klist,
        padding, {#2[[1]], missF[#1, #2[[2]]]} &, {{##}[[-1, 1]],
        Apply[missG, {##}[[All, 2]]]} &]
    ]

TimeSeriesListConvolve[ker_, list_, klist_: {-1, 1}, padding_: {}] :=
    TimeSeriesListConvolve[ker, list, klist, padding, Times, Plus]

TimeSeriesListCorrelate[ker_, rest__] :=
    TimeSeriesListConvolve[Reverse@ker, rest]

(* TimeSeriesGatherByDate, and time arguments for TimeSeriesMovingMap with named time period arguments *)

$BasicPeriods = {"Year", "Month", "Day", "Hour", "Minute", "Second"};

$BasicPeriodPositionRules = {"Year" -> 1, "Month" -> 2, "Day" -> 3, "Hour" -> 4, "Minute" -> 5, "Second" -> 6}

PeriodMappingFunction[r:(_String|{__String})]:=
	Which[
		MatchQ[r, Alternatives@@$BasicPeriods],
			DateList[#][[;; r /. $BasicPeriodPositionRules]]&,
		MatchQ[r, {Alternatives@@$BasicPeriods..}],
			DateList[#][[r /. $BasicPeriodPositionRules]]&,
		MatchQ[r, "Quarter"],
		With[{date = DateList[#]}, {date[[1]], Quotient[date[[2]] - 1, 3] + 1}]&
	]

TimeSeriesGatherByDate[series_, d:(_String|{__String})]:=
	GatherBy[series, PeriodMappingFunction[d][#[[1]]]&]

TimeSeriesGatherByDate[series_, f_]:=
	Block[{missF=MissingAlgebra@f}, GatherBy[series, missingF@First@#&]]

TimeSeriesGatherBy[series_, f_]:=
	Block[{missF=MissingAlgebra@f},GatherBy[series, missingF@Last@#&]]


(* Moving Maps *)

TimeSeriesMovingMap[f_, list_, r_] :=
    TimeSeriesListCorrelate[Array[1&, r], list, {-1,1},{},Times, f@{##}&]

TimeSeriesMovingMap[f_, list_, r:(_String|{__String})]:=
	With[{gather = TimeSeriesGatherByDate[list, r]},
		Function[series, {series[[-1,1]], f[series[[All,2]]]}]/@gather
	]

TimeSeriesMovingAverage[list_, r_] :=
    TimeSeriesMovingAverage[list, Array[1&, r]/r]

TimeSeriesMovingAverage[list_, wts_List] :=
    TimeSeriesListCorrelate[wts/Total@wts, list]

TimeSeriesMovingAverage[list_, r:(_String|{__String})]:=
	TimeSeriesMovingMap[Mean, list, r]

TimeSeriesMovingMedian[list_, r_] :=
    TimeSeriesListCorrelate[Array[1&, r], list, {-1,1},{},Times, Median@{##}&]

TimeSeriesMovingMedian[list_, r:(_String|{__String})]:=
	TimeSeriesMovingMap[Median, list, r]


(* Differences *)

TimeSeriesDifferences[list_, n_Integer:1]:=
	Nest[Function[l, TimeSeriesMovingMap[(#2-#1)&@@#&, l, 2]], list, n]

(* Ratios *)

TimeSeriesRatios[list_, n_Integer:1]:=
	Nest[Function[l, TimeSeriesMovingMap[(#2/#1)&@@#&, l, 2]], list, n]

(* Lag operator *)

TimeSeriesLag[list_, l_:1]:=
	Quiet[Check[Drop[Transpose@{list[[All,1]], RotateRight[list[[All,2]], l]},l],{},{Drop::drop}],{Drop::drop}]

(* Accumulate *)

TimeSeriesFold[f_, list_]:=
	Block[{missF=MissingAlgebra@f},
	FoldList[{#2[[1]], missF[#1[[2]], #2[[2]]]}&, First@list, Rest@list]
	]

TimeSeriesFoldList[f_, list_]:=
Block[{missF=MissingAlgebra@f},
	FoldList[{#2[[1]], missF[#1[[2]], #2[[2]]]}&, First@list, Rest@list]
]

TimeSeriesAccumulate[list_]:=
	TimeSeriesFoldList[Plus, list]

(* Normalize to First Element *)

TimeSeriesNormalize[list_, factor_:1]:=
With[{missF = If[FreeQ[list[[1,2]],Missing],factor #/list[[1,2]]&,Missing[NotAvailable]&]},
	TimeSeriesMap[missF , list]
]


(* Time series interpolation *)

Options[TimeSeriesInterpolation] = Options[Interpolation]


TimeSeriesInterpolation[series_,opts:OptionsPattern[]]:=
	With[{foo = Interpolation[TimeSeriesDateMap[AbsoluteTime, Select[series,FreeQ[#,Missing]&]],opts]},
		Function[time, foo[AbsoluteTime@time]]
	]

(* Time series fit *)

Options[TimeSeriesLinearFilter] =
	{"IdenticalIntervals"->False}

TimeSeriesLinearFilter[series_, functions_, vars_, OptionsPattern[]]:=
	Block[{lm, indices,missing, notmissing},
		notmissing = Select[series, FreeQ[#,Missing]&];
		missing = Select[series, Not@FreeQ[#,Missing]&];
		indices = If[OptionValue["IdenticalIntervals"], Range[Length@notmissing], AbsoluteTime /@ notmissing[[All,1]]];
		lm = LinearModelFit[Select[Transpose@{indices,notmissing[[All,2]]},FreeQ[#,_Missing]&], functions, vars];
		TimeSeriesMerge[{missing, Transpose@{notmissing[[All,1]], lm /@ indices}}]
	]

TimeSeriesSeasonFilter[series_, opts___]:=
	Block[{lm, months,coeffs, missing, notmissing,x},
		notmissing = Select[series, FreeQ[#,Missing]&];
		missing = Select[series, Not@FreeQ[#,Missing]&];
		months = Map[DateList, notmissing[[All,1]]][[All,2]];
		coeffs = Transpose[Rest@DeleteCases[Transpose[ReplacePart[Array[0&,12], {#->1}]&/@months],{0..}]];
		lm = LinearModelFit[MapThread[Append,{coeffs,notmissing[[All,2]]}], Array[x@#&, Length@coeffs[[1]]], Array[x@#&, Length@coeffs[[1]]], opts];
		Print@Normal@lm;
		TimeSeriesMerge[{missing, Transpose@{notmissing[[All,1]], lm@@@coeffs}}]
		]

(* Select *)

TimeSeriesSelect[series_, foo_, rest___]:=
	Select[series, foo[Last@#]&, rest]

(* Bins and time-weighted averages *)

TimeSeriesBinLists[series_, d:Alternatives[_String, _?NumericQ, {_?NumericQ, _String}]]:=
	TimeSeriesBinLists[series, {TimeSeriesDateMin@series, TimeSeriesDateMax@series, d}]

TimeSeriesBinLists[series_, {start_, end_, d_}] :=
 Block[{abstimes, absstart, absend, absd, bins},
  abstimes = AbsoluteTime /@ series[[All, 1]];
  absstart = AbsoluteTime@start; absend = AbsoluteTime@end;
  absd = Switch[d, _?NumericQ, d, _String,
    DatePlus[0, {1, d}], {_?NumericQ, _String}, DatePlus[0, d]];
  bins = BinLists[abstimes, {absstart, absend, absd}];
  Replace[bins, Rule @@@ Transpose@{abstimes, series}, {2}]]

TimeSeriesMean[series_] :=
 If[MatchQ[
   series, {}], {}, {DateList[
    Dot[AbsoluteTime /@ series[[All, 1]], series[[All, 2]]]/
     Total@series[[All, 2]]], Total@series[[All, 2]]}]

TimeSeriesBinMeans[series_, d_]:=
	TimeSeriesMean/@DeleteCases[TimeSeriesBinLists[series, d],{}]

TimeSeriesBinTotals[series_, d_]:=
	With[{dates = Sort@series[[All,1]]},
{#[[1,1]],Total@#[[All,2]]}&/@DeleteCases[TimeSeriesBinLists[series, d],{}]]

TimeSeriesDateMin[series_]:=
	DateList[Min[AbsoluteTime/@series[[All,1]]]]

TimeSeriesDateMax[series_]:=
	DateList[Max[AbsoluteTime/@series[[All,1]]]]


End[];
EndPackage[];