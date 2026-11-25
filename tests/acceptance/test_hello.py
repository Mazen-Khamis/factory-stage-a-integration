from hello import hello


def test_hello_returns_a_greeting():
    assert hello().startswith("Hello")
