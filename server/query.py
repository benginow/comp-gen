from pathlib import Path
import json
import pandas as pd
from dfply import filter_by, X, dfpipe, select, mutate
from functools import reduce
from datetime import datetime


def cmp_params(a):
    if a.name == "params":
        return a.map(lambda x: x.replace("_", "x").split("x")).map(
            lambda l: reduce(lambda x, y: x * y, map(int, l))
        )
    else:
        return a


def latest_date():
    dates = set()
    for config_path in Path("completed").glob("**/config.json"):
        # exp_path = Path(config_path.parents[0])
        config = json.load(config_path.open("r"))

        dates.add(datetime.strptime(config["date"], "%b%d-%H%M"))

    latest = list(sorted(dates))[-1]
    return latest.strftime("%b%d-%H%M")


@dfpipe
def pivot_table(df, **kwargs):
    df = pd.pivot_table(df, **kwargs)
    return df.reset_index(drop=True, names=["index"])


@dfpipe
def reset_index(df, **kwargs):
    return df.reset_index(**kwargs)


@dfpipe
def sort_values(df, **kwargs):
    return df.sort_values(**kwargs)


@dfpipe
def to_csv(df, path, **kwargs):
    df.to_csv(path, **kwargs)
    print(f"Wrote {path}")
    return df


@dfpipe
def display(df):
    print(df.to_string())
    return df


def exp_iter(name, date=None):
    res = []
    for config_path in Path("completed").glob("**/config.json"):
        exp_path = Path(config_path.parents[0])
        config = json.load(config_path.open("r"))

        if "metadata" not in config:
            continue

        if all(
            [
                "Mar20" in config["date"],
                "expanding" in config["metadata"]["rules.json"],
                name in config["name"],
            ]
        ):
            df = (
                pd.read_csv(exp_path / "data.csv")
                >> filter_by((X.name == "nodes") | (X.name == "cost"))
                >> filter_by(X.iteration != "report")
                >> pivot_table(
                    index=["phase", "iteration"],
                    columns=["name"],
                    values="value",
                    sort=False,
                )
                >> mutate(pruning=config["metadata"]["alt_cost"])
                >> select(["pruning", "cost", "nodes"])
            )
            res += [df]

    out = Path("figs") / "data" / "2d-conv-3x3_3x3_iter.csv"
    final = pd.concat(res)
    final.to_csv(out, index_label="index")
    print(final)
    print(f"Wrote {out}")


def compile_est_cycles():
    res = []
    for config_path in Path("completed").glob("**/config.json"):
        exp_path = Path(config_path.parents[0])
        config = json.load(config_path.open("r"))

        if "metadata" not in config:
            continue

        name, params = config["name"].split("_", 1)
        cycles_csv = exp_path / "results" / f"{name}.csv"

        if all([
                "Mar20" in config["date"],
                cycles_csv.exists(),
        ]):
            ruleset = Path(config["metadata"]["rules.json"]).stem
            print(ruleset)
            df = (
                pd.read_csv(cycles_csv)
                >> mutate(
                    benchmark=name,
                    params=params,
                    ruleset=ruleset,
                    greedy=config["metadata"]["alt_cost"]
                )
                >> select([
                    "kernel",
                    "benchmark",
                    "params",
                    "ruleset",
                    "greedy",
                    "cycles"
                ])
            )
            res.append(df)
            print(json.dumps(config, indent=2))
            # print(df[df["kernel"] == "compgen"]["cycles"])

    df = (pd.concat(res)
          >> sort_values(by=["benchmark", "params"], key=cmp_params)
          >> reset_index(drop=True, names=["index"])
          >> display()
          >> to_csv(
              Path("figs") / "data" / "est_cycles.csv",
              index=False
          ))


def compile_times():
    res = []
    for config_path in Path("completed").glob("**/config.json"):
        exp_path = Path(config_path.parents[0])
        config = json.load(config_path.open("r"))

        if "metadata" not in config:
            continue

        if all(
            [
                "Mar20" in config["date"],
                "expanding" in config["metadata"]["rules.json"],
            ]
        ):
            memory = pd.read_csv(
                exp_path / "memory.csv", header=None, names=["timestamp", "ram_used"]
            )
            df = memory.agg(["min", "max"])
            max_ts = df.loc[["max"]]["timestamp"].values[0]
            min_ts = df.loc[["min"]]["timestamp"].values[0]
            killed = "killed" in list(memory["ram_used"].values)
            res.append(
                [
                    config["name"],
                    "pruning" if config["metadata"]["alt_cost"] else "stock",
                    max_ts - min_ts,
                    killed,
                ]
            )

    out = Path("figs") / "data" / "compile_times.csv"
    df = pd.DataFrame(res, columns=["benchmark", "type", "runtime", "killed"])
    df.to_csv(out, index_label="index")
    print(df)
    print(f"Wrote {out}")


def scheduler():
    runtime = []
    cost = []
    for config_path in Path("completed").glob("**/config.json"):
        exp_path = Path(config_path.parents[0])
        config = json.load(config_path.open("r"))

        if "metadata" not in config:
            continue

        if all(["Mar23" in config["date"]]):
            memory = pd.read_csv(
                exp_path / "memory.csv", header=None, names=["timestamp", "ram_used"]
            )
            df = memory.agg(["min", "max"])
            max_ts = df.loc[["max"]]["timestamp"].values[0]
            min_ts = df.loc[["min"]]["timestamp"].values[0]
            runtime.append([config["name"], max_ts - min_ts])

            benchmark, params = config["name"].split("_", 1)
            df = (pd.read_csv(exp_path / "data.csv")
                  >> filter_by(X.name == "cost")
                  >> filter_by(X.iteration != "report")
                  >> mutate(benchmark=benchmark, params=params)
                  >> select(["benchmark", "params", "iteration", "value"]))
            cost += [df]

    # write data to csv
    df = pd.DataFrame(runtime, columns=["benchmark", "runtime"])
    out = Path("figs") / "data" / "backoff_fail.csv"
    df.to_csv(out, index_label="index")
    print(f"Wrote {out}")

    # write cost data to csv
    df = (pd.concat(cost) >> reset_index(drop=True))
    out = Path("figs") / "data" / "backoff_cost.csv"
    df.to_csv(out)
    print(f"Wrote {out}")


def play():
    pass
    # res = []
    # for config_path in Path("completed").glob("**/config.json"):
    #     exp_path = Path(config_path.parents[0])
    #     config = json.load(config_path.open("r"))

    #     if all(["Mar23" in config["date"]]):
    #         print(json.dumps(config, indent=2))
    # df = pd.concat(res)
    # print(df.to_string())


def main():
    # exp_iter("2d-conv_3x3_3x3")
    # compile_est_cycles()
    # compile_times()
    scheduler()
    # play()


# if __name__ == "__main__":
main()
