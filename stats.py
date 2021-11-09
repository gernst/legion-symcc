from xml.etree import ElementTree
import bz2
import urllib.request
import io
import re
import sys

START = "https://test-comp.sosy-lab.org/2022/results/results-verified/"
END = ".merged.xml.bz2\n"

def avg(xs):
    return sum(xs) / len(xs) if xs else 0.0

def open_url(url):
    return urllib.request.urlopen(url)

def score_from_run(node):
    columns = [column for column in node if column.get("title") == "score"]
    if len(columns) == 0:
        return 0
    assert len(columns) == 1
    first, = columns
    return float(first.get("value"))

def scores_from_result(result):
    return [score_from_run(node) for node in result if node.tag == "run"]

def date_from_result(result):
    return result.get("date")

def category_from_result(result):
    return result.get("block")

def result_from_url(url):
    with open_url(url) as stream:
        stream = bz2.BZ2File(stream)
        result = ElementTree.ElementTree().parse(stream)
        return result

def urls_from_eml(file):
    with open(file, "rt") as stream:
        return [line.strip() for line in stream.readlines() if line.startswith(START) and line.endswith(END)]

def score_percentage_for_category(category, column):
    if category in column:
        scores = column[category]
        return avg(scores)
    else:
        return ""

def score_percentage(column):
    scores = [score_percentage_for_category(category, column) for category in column]
    return sum(scores)

def average_category_size(column):
    sizes = [len(column[category]) for category in column]
    return avg(sizes)

def score_normalized(column):
    return score_percentage(column) * average_category_size(column)

if __name__ == "__main__":
    file = sys.argv[1]
    urls = urls_from_eml(file)

    categories = set()
    dates = set()

    table = {} # column first

    for url in urls:
        result = result_from_url(url)

        date = date_from_result(result)
        category = category_from_result(result)
        scores = scores_from_result(result)
        score = sum(scores)

        # print("%s %s: %.2f" % (date, category, score))

        if date not in dates:
            dates.add(date)
            table[date] = {}

        if category not in categories:
            categories.add(category)

        table[date][category] = scores

    dates = sorted(list(dates))
    categories = sorted(list(categories))

    header = [""] + dates
    print(";".join(header))

    for category in categories:
        row = [category] + [str(sum(table[date][category])) for date in dates]
        print(";".join(row))
    
    footer = [""] + [str(score_normalized(table[date])) for date in dates]
    print(";".join(footer))

